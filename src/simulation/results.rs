//! Structs holding the results of a simulation.
use crate::agent::{agent_index, AgentIndex};
use crate::event::{Event, EventQueue};
use crate::mode::{AggregateModeResults, Mode, ModeIndex, ModeResults, PreDayChoices};
use crate::network::NetworkWeights;
use crate::schedule_utility::ScheduleUtility;
use crate::units::{Distribution, Time, Utility};

use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::BufReader;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::path::{Path, PathBuf};
use ttf::TTFNum;

/// Struct to store the results of a [Simulation](super::Simulation).
#[derive(Clone, Debug, Default)]
pub struct SimulationResults<T> {
    /// [AggregateResults] of each iteration.
    pub iterations: Vec<AggregateResults<T>>,
    /// [IterationResults] of the last iteration.
    pub last_iteration: Option<IterationResults<T>>,
}

impl<T: TTFNum> SimulationResults<T> {
    /// Create an empty SimulationResults.
    pub fn new() -> Self {
        SimulationResults::default()
    }

    /// Reads [SimulationResults] from an output directory.
    pub fn from_output_dir(output_dir: &Path) -> Self {
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

    /// Appends the [AggregateResults] of an iteration to the [SimulationResults].
    pub fn push_iteration(&mut self, iteration: AggregateResults<T>) {
        self.iterations.push(iteration);
    }
}

/// Aggregate results summarizing the results of an iteration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AggregateResults<T> {
    /// Distribution of the surplus of the agents.
    pub surplus: Distribution<Utility<T>>,
    /// Mode-specific aggregate results.
    pub mode_results: AggregateModeResults<T>,
}

/// Detailed results of an iteration.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(bound(deserialize = "T: TTFNum"))]
pub struct IterationResults<T> {
    /// Agent-specific results.
    pub agent_results: AgentResults<T>,
    /// Simulated weights of the network.
    pub weights: NetworkWeights<T>,
}

impl<T> IterationResults<T> {
    /// Creates a new IterationResults.
    pub fn new(agent_results: AgentResults<T>, weights: NetworkWeights<T>) -> Self {
        IterationResults {
            agent_results,
            weights,
        }
    }

    /// Returns a reference to the [AgentResults].
    pub fn agent_results(&self) -> &AgentResults<T> {
        &self.agent_results
    }

    /// Returns a reference to the [NetworkWeights].
    pub fn network_weights(&self) -> &NetworkWeights<T> {
        &self.weights
    }

    /// Returns the [NetworkWeights], consuming the IterationResults.
    pub fn into_network_weights(self) -> NetworkWeights<T> {
        self.weights
    }

    /// Iterates over the [AgentIndex] and [AgentResult] of the [IterationResults].
    pub fn iter_agent_results(&self) -> impl Iterator<Item = (AgentIndex, &AgentResult<T>)> {
        self.agent_results
            .iter()
            .enumerate()
            .map(|(i, r)| (agent_index(i), r))
    }
}

/// Results from the pre-day choices of an agent.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct PreDayResult<T> {
    /// Index of the chosen mode.
    mode: ModeIndex,
    /// Expected utility from the trip.
    expected_utility: Utility<T>,
    /// Mode-specific pre-day results.
    choices: PreDayChoices<T>,
}

impl<T> PreDayResult<T> {
    /// Creates a new PreDayResult.
    pub fn new(mode: ModeIndex, expected_utility: Utility<T>, choices: PreDayChoices<T>) -> Self {
        PreDayResult {
            mode,
            expected_utility,
            choices,
        }
    }

    /// Returns a reference to the [PreDayChoices].
    pub fn get_choices(&self) -> &PreDayChoices<T> {
        &self.choices
    }

    /// Returns the index of the chosen mode.
    pub fn get_mode_index(&self) -> ModeIndex {
        self.mode
    }
}

impl<T: Copy> PreDayResult<T> {
    /// Returns the expected utility.
    pub fn get_expected_utility(&self) -> Utility<T> {
        self.expected_utility
    }
}

impl<T: TTFNum + 'static> PreDayResult<T> {
    /// Converts the [PreDayResult] into an [AgentResult].
    pub fn into_agent_result(self, agent_id: usize) -> AgentResult<T> {
        let mode_results = self.choices.init_mode_results();
        AgentResult::new(agent_id, self, mode_results)
    }

    /// Returns the event (if any) associated with the pre-day choices.
    pub fn get_event(&self, agent: AgentIndex) -> Option<Box<dyn Event<T>>> {
        self.choices.get_event(agent)
    }
}

/// Results of an agent, during a single iteration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AgentResult<T> {
    /// Id of the agent.
    id: usize,
    /// Utility resulting from the trip.
    utility: Option<Utility<T>>,
    /// Departure time from origin.
    departure_time: Option<Time<T>>,
    /// Arrival time at destination.
    arrival_time: Option<Time<T>>,
    /// Results from the pre-day model.
    pre_day_results: PreDayResult<T>,
    /// Mode-specific results.
    mode_results: ModeResults<T>,
}

impl<T> AgentResult<T> {
    /// Creates a new AgentResult.
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

    /// Returns the id of the agent.
    pub fn id(&self) -> usize {
        self.id
    }

    /// Returns a reference to the [PreDayResult].
    pub fn pre_day_results(&self) -> &PreDayResult<T> {
        &self.pre_day_results
    }

    /// Returns a reference to the [ModeResults].
    pub fn mode_results(&self) -> &ModeResults<T> {
        &self.mode_results
    }

    /// Returns a mutable reference to the [ModeResults].
    pub fn mut_mode_results(&mut self) -> &mut ModeResults<T> {
        &mut self.mode_results
    }

    /// Sets the departure time to the given value.
    pub fn set_departure_time(&mut self, departure_time: Time<T>) {
        self.departure_time = Some(departure_time);
    }

    /// Sets the arrival time to the given value.
    pub fn set_arrival_time(&mut self, arrival_time: Time<T>) {
        self.arrival_time = Some(arrival_time);
    }

    /// Returns `true` if the agent has arrived at destination.
    pub fn has_arrived(&self) -> bool {
        self.arrival_time.is_some()
    }
}

impl<T: Copy> AgentResult<T> {
    /// Returns the utility of the agent.
    pub fn utility(&self) -> Option<Utility<T>> {
        self.utility
    }

    /// Returns the departure time of the agent.
    pub fn departure_time(&self) -> Option<Time<T>> {
        self.departure_time
    }

    /// Returns the arrival time of the agent.
    pub fn arrival_time(&self) -> Option<Time<T>> {
        self.arrival_time
    }
}

impl<T: TTFNum> AgentResult<T> {
    /// Computes and sets the utility of the agent.
    ///
    /// The utility is computed from the given [ScheduleUtility] and [Mode] description, and the
    /// stored [ModeResults].
    pub fn compute_utility(&mut self, schedule_utility: &ScheduleUtility<T>, mode: &Mode<T>) {
        self.utility = Some(mode.get_utility(
            &self.mode_results,
            schedule_utility,
            self.departure_time,
            self.arrival_time,
        ));
    }
}

/// Struct to store the [AgentResult] of each agent in the Simulation.
#[derive(Debug, Default, Clone, Deserialize, Serialize)]
pub struct AgentResults<T>(Vec<AgentResult<T>>);

impl<T> AgentResults<T> {
    /// Creates a new empty AgentResults, with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        AgentResults(Vec::with_capacity(capacity))
    }
}

impl<T: Copy> AgentResults<T> {
    /// Iterates over the departure times of the agents.
    pub fn departure_times(&self) -> impl Iterator<Item = Option<Time<T>>> + '_ {
        self.iter().map(|r| r.departure_time)
    }
}

impl<T: TTFNum + 'static> AgentResults<T> {
    /// Returns an [EventQueue] with all the events resulting from the pre-day choices of the
    /// agents.
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
