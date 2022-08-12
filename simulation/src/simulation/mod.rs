pub mod parameters;
pub mod preprocess;

use crate::agent::{agent_index, Agent, AgentIndex};
use crate::event::{Event, EventQueue};
use crate::mode::road::AggregateRoadResults;
use crate::mode::{
    AggregateConstantResults, AggregateModeResults, Mode, ModeIndex, ModeResults, PreDayChoices,
};
use crate::network::{Network, NetworkSkim, NetworkWeights};
use crate::schedule_utility::ScheduleUtility;
use crate::units::{Distribution, Time, Utility};
use parameters::Parameters;
use preprocess::PreprocessingData;

use anyhow::{anyhow, Result};
use askama::Template;
use indicatif::{ProgressBar, ProgressStyle};
use log::{debug, info, log_enabled, Level};
use object_pool::Pool;
use rand::prelude::*;
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::{BufReader, Write};
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::path::{Path, PathBuf};
use ttf::TTFNum;

/// An abstract representation of an area to be simulated.
///
/// A simulation is composed of the following items:
///
/// - A set of [agents](Agent) performing trips.
/// - A representation of the [Network], where trips can take place.
/// - A [Parameters] instance.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Simulation")]
#[schemars(description = "")]
pub struct Simulation<T> {
    #[serde(default)]
    agents: Vec<Agent<T>>,
    network: Network<T>,
    parameters: Parameters<T>,
}

impl<T: TTFNum + Serialize + 'static> Simulation<T> {
    /// Run the simulation, starting from free-flow weights, and return a [SimulationResults]
    /// instance.
    pub fn run(&self, output_dir: &Path) -> Result<()> {
        let weights = self.network.get_free_flow_weights();
        self.run_from_weights(weights, output_dir)
    }

    /// Run the simulation, using the given [NetworkWeights] as initial weights of the network, and
    /// return a [SimulationResults] instance.
    pub fn run_from_weights(
        &self,
        init_weights: NetworkWeights<T>,
        output_dir: &Path,
    ) -> Result<()> {
        let preprocess_data = self.preprocess();
        let mut weights = init_weights;
        let mut prev_agent_results = None;
        let mut iteration_counter: u64 = 1;
        let mut sim_results = SimulationResults::new();
        loop {
            info!("===== Iteration {} =====", iteration_counter);
            info!("Computing skims");
            let skims = self.network.compute_skims(
                &weights,
                &preprocess_data.network,
                &self.parameters.network,
            )?;
            let iteration_results = self.run_iteration(
                &weights,
                skims,
                prev_agent_results.as_ref(),
                iteration_counter,
            )?;
            let aggregate_results =
                self.compute_aggregate_results(&iteration_results, prev_agent_results.as_ref());
            self.parameters.save_aggregate_results(
                &aggregate_results,
                iteration_counter,
                output_dir,
            )?;
            sim_results.push_iteration(aggregate_results);
            info!("Checking stopping rules");
            if self.parameters.stop(
                iteration_counter,
                iteration_results.agent_results(),
                prev_agent_results.as_ref(),
            ) {
                info!("Stopping simulation");
                sim_results.last_iteration = Some(iteration_results);
                info!("Writing report");
                self.write_report(&sim_results, output_dir)?;
                info!("Saving detailed results");
                self.parameters
                    .save_iteration_results(sim_results.last_iteration.unwrap(), output_dir)?;
                break;
            }
            iteration_counter += 1;
            info!("Computing weights");
            (weights, prev_agent_results) = (
                iteration_results.weights,
                Some(iteration_results.agent_results),
            );
        }
        Ok(())
    }

    /// Compute everything that can be computed before the first iteration of the simulation and
    /// return a [PreprocessingData] instance with the results of these computations.
    pub fn preprocess(&self) -> PreprocessingData {
        // Run the preprocessing stuff related to the network.
        let network = self.network.preprocess(&self.agents);
        PreprocessingData { network }
    }

    /// Run an iteration given the current [NetworkWeights], the associated [NetworkSkim] and the
    /// [IterationResults] of the previous iteration (if any).
    ///
    /// An iteration consist in running successively the pre-day model, the within-day model and
    /// the day-to-day model.
    pub fn run_iteration(
        &self,
        weights: &NetworkWeights<T>,
        skims: NetworkSkim<T>,
        previous_results_opt: Option<&AgentResults<T>>,
        iteration_counter: u64,
    ) -> Result<IterationResults<T>> {
        let pre_day_results =
            self.run_pre_day_model(&skims, previous_results_opt, iteration_counter)?;
        info!("Running within-day model");
        let (sim_weights, within_day_results) = self.run_within_day_model(pre_day_results, &skims);
        info!("Running day-to-day model");
        let new_weights = self.run_day_to_day_model(weights, &sim_weights, iteration_counter);
        crate::show_stats();
        Ok(IterationResults::new(within_day_results, new_weights))
    }

    /// Returns the [queue of events](EventQueue) generated by the pre-day model, given the expected
    /// [skims of the network](NetworkSkim).
    ///
    /// The pre-day model represents the decisions made by the agents before the start of a
    /// simulated day. In particular, agents choose their mode and departure time during the
    /// pre-day model.
    pub fn run_pre_day_model(
        &self,
        exp_skims: &NetworkSkim<T>,
        previous_results_opt: Option<&AgentResults<T>>,
        iteration_counter: u64,
    ) -> Result<PreDayResults<T>> {
        let pool = Pool::new(rayon::current_num_threads(), Default::default);
        info!("Running pre-day model");
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(self.agents.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .progress_chars("█░"),
        );
        let results = if let Some(previous_results) = previous_results_opt {
            let updates = self.get_update_vector(iteration_counter);
            (&self.agents, previous_results.deref(), updates)
                .into_par_iter()
                .map_init(
                    || pool.pull(Default::default),
                    |alloc, (agent, prev_agent_result, update)| {
                        bp.inc(1);
                        agent.make_pre_day_choice(
                            exp_skims,
                            Some(prev_agent_result.pre_day_results()),
                            update,
                            alloc,
                        )
                    },
                )
                .collect::<Result<Vec<_>, _>>()?
        } else {
            // Everyone has to make a choice.
            self.agents
                .par_iter()
                .map_init(
                    || pool.pull(Default::default),
                    |alloc, agent| {
                        bp.inc(1);
                        agent.make_pre_day_choice(exp_skims, None, true, alloc)
                    },
                )
                .collect::<Result<Vec<_>, _>>()?
        };
        bp.finish_and_clear();
        Ok(PreDayResults(results))
    }

    pub fn run_within_day_model(
        &self,
        pre_day_results: PreDayResults<T>,
        skims: &NetworkSkim<T>,
    ) -> (NetworkWeights<T>, AgentResults<T>) {
        debug!("Initializing variables");
        let mut state = self.network.get_blank_state();
        let mut results = self.init_agent_results(pre_day_results);
        let mut events = results.get_event_queue();
        let mut nb_events = 0;
        info!("Executing events");
        let bp = if log_enabled!(Level::Info) {
            ProgressBar::new(events.len() as u64)
        } else {
            ProgressBar::hidden()
        };
        bp.set_style(
            ProgressStyle::default_bar()
                .template("{bar:60} ETA: {eta}")
                .progress_chars("█░"),
        );
        while let Some(event) = events.pop() {
            nb_events += 1;
            if let Some(result) = event.get_agent_index().map(|id| &mut results[id]) {
                // The event is associated to an agent.
                event.execute(&self.network, skims, &mut state, Some(result), &mut events);
                if result.has_arrived() {
                    bp.inc(1);
                }
            } else {
                event.execute(&self.network, skims, &mut state, None, &mut events);
            }
        }
        bp.finish_and_clear();
        // Drop the events queue (it is empty) so that it no longer borrows the results.
        drop(events);
        debug!("Succesfully executed {} events", nb_events);
        // Compute network weights.
        debug!("Computing network weights");
        let weights = state.get_weights(&self.parameters);
        // Compute agent utilities.
        debug!("Computing agent utilities");
        for (i, r) in results.iter_mut().enumerate() {
            let chosen_mode = r.pre_day_results().get_mode_index();
            r.compute_utility(
                self.agents[i].schedule_utility(),
                &self.agents[i][chosen_mode],
            );
        }
        (weights, results)
    }

    pub fn run_day_to_day_model(
        &self,
        old_weights: &NetworkWeights<T>,
        weights: &NetworkWeights<T>,
        iteration_counter: u64,
    ) -> NetworkWeights<T> {
        self.parameters
            .learn(old_weights, weights, iteration_counter)
    }

    pub fn compute_aggregate_results(
        &self,
        results: &IterationResults<T>,
        prev_agent_results_opt: Option<&AgentResults<T>>,
    ) -> AggregateResults<T> {
        let surplus = Distribution::from_iterator(
            results
                .iter_agent_results()
                .map(|(_agent_id, r)| r.pre_day_results().get_expected_utility()),
        )
        .unwrap();
        let mut road_entries = Vec::with_capacity(self.agents.len());
        let mut cst_entries = Vec::with_capacity(self.agents.len());
        if let Some(prev_agent_results) = prev_agent_results_opt {
            for ((agent_id, agent_result), prev_agent_result) in
                results.iter_agent_results().zip(prev_agent_results.iter())
            {
                let mode_id = agent_result.pre_day_results().get_mode_index();
                match &self.agents[agent_id.index()][mode_id] {
                    Mode::Road(road_mode) => {
                        road_entries.push((road_mode, agent_result, Some(prev_agent_result)))
                    }
                    Mode::Constant(_) => cst_entries.push(agent_result),
                }
            }
        } else {
            for (agent_id, agent_result) in results.iter_agent_results() {
                let mode_id = agent_result.pre_day_results().get_mode_index();
                match &self.agents[agent_id.index()][mode_id] {
                    Mode::Road(road_mode) => road_entries.push((road_mode, agent_result, None)),
                    Mode::Constant(_) => cst_entries.push(agent_result),
                }
            }
        }
        let road_results = if road_entries.is_empty() {
            None
        } else {
            Some(AggregateRoadResults::from_agent_results(
                road_entries,
                self.network
                    .get_road_network()
                    .expect("Found RoadResults but no road network"),
            ))
        };
        let cst_results = if cst_entries.is_empty() {
            None
        } else {
            Some(AggregateConstantResults::from_agent_results(cst_entries))
        };
        let mode_results = AggregateModeResults {
            road: road_results,
            constant: cst_results,
        };
        AggregateResults {
            surplus,
            mode_results,
        }
    }

    fn init_agent_results(&self, pre_day_results: PreDayResults<T>) -> AgentResults<T> {
        let mut results = AgentResults::with_capacity(pre_day_results.len());
        for (agent, pre_day_result) in self.agents.iter().zip(pre_day_results.into_iter()) {
            results.push(pre_day_result.into_agent_result(agent.id));
        }
        results
    }

    /// Build a vector of boolean indicating the agents that can switch their choice for the next
    /// iteration.
    fn get_update_vector(&self, iteration_counter: u64) -> Vec<bool> {
        // To change the seed from one iteration to another, we add the iteration number to the
        // default seed.
        let mut rng = if let Some(seed) = self.parameters.random_seed {
            XorShiftRng::seed_from_u64(seed + iteration_counter as u64)
        } else {
            XorShiftRng::from_entropy()
        };
        let mut updates = vec![true; self.agents.len()];
        // Number of agents that will be able to switch their choice.
        let n = (self.parameters.update_ratio * self.agents.len() as f64) as usize;
        updates[n..].fill(false);
        updates.shuffle(&mut rng);
        updates
    }

    pub fn write_report(&self, results: &SimulationResults<T>, output_dir: &Path) -> Result<()> {
        let report_results = self.build_report(results)?;
        let filename: PathBuf = [output_dir.to_str().unwrap(), "report.html"]
            .iter()
            .collect();
        let mut file = File::create(&filename)?;
        file.write_all(report_results.render().unwrap().as_bytes())?;
        Ok(())
    }

    fn build_report(&self, results: &SimulationResults<T>) -> Result<ReportResults<T>> {
        if let Some(last_iteration) = &results.last_iteration {
            let mut road_departure_times = Vec::with_capacity(self.agents.len());
            for (agent_id, agent_result) in last_iteration.iter_agent_results() {
                let mode_id = agent_result.pre_day_results().get_mode_index();
                match &self.agents[agent_id.index()][mode_id] {
                    Mode::Road(_) => {
                        road_departure_times.push(agent_result.departure_time().unwrap());
                    }
                    Mode::Constant(_) => (),
                }
            }

            let last_iteration = IterationStatistics {
                road_departure_times,
            };
            Ok(ReportResults {
                iterations: results.iterations.clone(),
                last_iteration,
            })
        } else {
            Err(anyhow!("Cannot build report without last iteration"))
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct SimulationResults<T> {
    pub iterations: Vec<AggregateResults<T>>,
    pub last_iteration: Option<IterationResults<T>>,
}

impl<T: TTFNum> SimulationResults<T> {
    fn new() -> Self {
        SimulationResults::default()
    }

    fn push_iteration(&mut self, iteration: AggregateResults<T>) {
        self.iterations.push(iteration);
    }
}

pub fn read_output<T: TTFNum>(output_dir: &Path) -> SimulationResults<T> {
    let mut iterations = Vec::new();
    let mut iteration_counter = 1;
    loop {
        let filename: PathBuf = [
            output_dir.to_str().unwrap(),
            &format!("iteration{iteration_counter}.json"),
        ]
        .iter()
        .collect();
        if let Ok(file) = File::open(filename) {
            let reader = BufReader::new(file);
            let it = serde_json::from_reader(reader).expect("Unable to parse AggregateResults");
            iterations.push(it);
        } else {
            break;
        }
        iteration_counter += 1;
    }
    let filename: PathBuf = [output_dir.to_str().unwrap(), "results.json"]
        .iter()
        .collect();
    let last_iteration = if let Ok(file) = File::open(filename) {
        let reader = BufReader::new(file);
        Some(serde_json::from_reader(reader).expect("Unable to parse IterationResults"))
    } else {
        None
    };
    SimulationResults {
        iterations,
        last_iteration,
    }
}

struct IterationStatistics<T> {
    road_departure_times: Vec<Time<T>>,
}

#[derive(Template)]
#[template(path = "report.html")]
struct ReportResults<T: TTFNum> {
    pub iterations: Vec<AggregateResults<T>>,
    pub last_iteration: IterationStatistics<T>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateResults<T> {
    surplus: Distribution<Utility<T>>,
    mode_results: AggregateModeResults<T>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct IterationResults<T> {
    agent_results: AgentResults<T>,
    weights: NetworkWeights<T>,
}

impl<T> IterationResults<T> {
    fn new(agent_results: AgentResults<T>, weights: NetworkWeights<T>) -> Self {
        IterationResults {
            agent_results,
            weights,
        }
    }

    pub fn agent_results(&self) -> &AgentResults<T> {
        &self.agent_results
    }

    pub fn network_weights(&self) -> &NetworkWeights<T> {
        &self.weights
    }

    pub fn into_network_weights(self) -> NetworkWeights<T> {
        self.weights
    }

    pub fn iter_agent_results(&self) -> impl Iterator<Item = (AgentIndex, &AgentResult<T>)> {
        self.agent_results
            .iter()
            .enumerate()
            .map(|(i, r)| (agent_index(i), r))
    }
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct PreDayResult<T> {
    mode: ModeIndex,
    expected_utility: Utility<T>,
    choices: PreDayChoices<T>,
}

impl<T> PreDayResult<T> {
    pub fn new(mode: ModeIndex, expected_utility: Utility<T>, choices: PreDayChoices<T>) -> Self {
        PreDayResult {
            mode,
            expected_utility,
            choices,
        }
    }

    pub fn get_choices(&self) -> &PreDayChoices<T> {
        &self.choices
    }

    pub fn get_mode_index(&self) -> ModeIndex {
        self.mode
    }
}

impl<T: Copy> PreDayResult<T> {
    pub fn get_expected_utility(&self) -> Utility<T> {
        self.expected_utility
    }
}

impl<T: TTFNum + 'static> PreDayResult<T> {
    fn into_agent_result(self, agent_id: usize) -> AgentResult<T> {
        let mode_results = self.choices.init_mode_results();
        AgentResult::new(agent_id, self, mode_results)
    }

    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        self.choices.get_event(agent)
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct PreDayResults<T>(Vec<PreDayResult<T>>);

impl<T> IntoIterator for PreDayResults<T> {
    type Item = PreDayResult<T>;
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> Index<AgentIndex> for PreDayResults<T> {
    type Output = PreDayResult<T>;

    fn index(&self, index: AgentIndex) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl<T> Deref for PreDayResults<T> {
    type Target = Vec<PreDayResult<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AgentResult<T> {
    id: usize,
    utility: Option<Utility<T>>,
    departure_time: Option<Time<T>>,
    arrival_time: Option<Time<T>>,
    pre_day_results: PreDayResult<T>,
    mode_results: ModeResults<T>,
}

impl<T> AgentResult<T> {
    pub fn new(id: usize, pre_day_results: PreDayResult<T>, mode_results: ModeResults<T>) -> Self {
        AgentResult {
            id,
            utility: None,
            departure_time: None,
            arrival_time: None,
            pre_day_results,
            mode_results,
        }
    }

    pub fn pre_day_results(&self) -> &PreDayResult<T> {
        &self.pre_day_results
    }

    pub fn mode_results(&self) -> &ModeResults<T> {
        &self.mode_results
    }

    pub fn mut_mode_results(&mut self) -> &mut ModeResults<T> {
        &mut self.mode_results
    }

    pub fn set_departure_time(&mut self, departure_time: Time<T>) {
        self.departure_time = Some(departure_time);
    }

    pub fn set_arrival_time(&mut self, arrival_time: Time<T>) {
        self.arrival_time = Some(arrival_time);
    }

    pub fn has_arrived(&self) -> bool {
        self.arrival_time.is_some()
    }
}

impl<T: Copy> AgentResult<T> {
    pub fn utility(&self) -> Option<Utility<T>> {
        self.utility
    }

    pub fn departure_time(&self) -> Option<Time<T>> {
        self.departure_time
    }

    pub fn arrival_time(&self) -> Option<Time<T>> {
        self.arrival_time
    }
}

impl<T: TTFNum> AgentResult<T> {
    pub fn compute_utility(&mut self, schedule_utility: &ScheduleUtility<T>, mode: &Mode<T>) {
        self.utility = Some(mode.get_utility(
            &self.mode_results,
            schedule_utility,
            self.departure_time,
            self.arrival_time,
        ));
    }
}

#[derive(Debug, Default, Clone, Deserialize, Serialize)]
pub struct AgentResults<T>(Vec<AgentResult<T>>);

impl<T> AgentResults<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        AgentResults(Vec::with_capacity(capacity))
    }
}

impl<T: Copy> AgentResults<T> {
    pub fn departure_times(&self) -> impl Iterator<Item = Option<Time<T>>> + '_ {
        self.iter().map(|r| r.departure_time)
    }
}

impl<T: TTFNum + 'static> AgentResults<T> {
    pub fn get_event_queue(&self) -> EventQueue<T> {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(id, r)| r.pre_day_results().get_event(AgentIndex::new(id)))
            .collect()
    }
}

impl<T> Index<AgentIndex> for AgentResults<T> {
    type Output = AgentResult<T>;

    fn index(&self, index: AgentIndex) -> &Self::Output {
        &self.0[index.index()]
    }
}

impl<T> IndexMut<AgentIndex> for AgentResults<T> {
    fn index_mut(&mut self, index: AgentIndex) -> &mut Self::Output {
        &mut self.0[index.index()]
    }
}

impl<T> Deref for AgentResults<T> {
    type Target = Vec<AgentResult<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for AgentResults<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
