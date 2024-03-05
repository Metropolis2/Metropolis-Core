// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to agents.
use std::ops::Index;

use anyhow::{anyhow, Context, Result};
use choice::ChoiceModel;
use itertools;
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::mode::{mode_index, Mode, ModeIndex};
use crate::network::road_network::skim::EAAllocation;
use crate::network::{Network, NetworkSkim, NetworkWeights};
use crate::progress_bar::MetroProgressBar;
use crate::simulation::results::AgentResult;
use crate::simulation::PreprocessingData;
use crate::units::{Interval, NoUnit};

/// Representation of an independent and intelligent agent that makes one trip per day.
///
/// An agent is characterized by:
///
/// - A set of [modes](Mode) that he/she can take to perform his/her trip.
/// - A [ChoiceModel] describing how his/her mode is chosen, given the expected utilities for each
/// mode.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound = "T: TTFNum")]
#[schemars(title = "Agent")]
#[schemars(description = "Abstract representation of an individual that makes one trip per day.")]
#[schemars(bound = "T: TTFNum + JsonSchema")]
#[schemars(example = "crate::schema::example_agent")]
pub struct Agent<T> {
    /// Id used when writing the results of the agents.
    #[serde(default)]
    pub id: usize,
    /// Modes accessible to the agent.
    #[validate(length(min = 1))]
    pub(crate) modes: Vec<Mode<T>>,
    /// Choice model used for mode choice.
    ///
    /// When not specified, the first mode is always chosen.
    #[serde(default)]
    pub(crate) mode_choice: Option<ChoiceModel<NoUnit<T>>>,
}

impl<T> Agent<T> {
    /// Creates a new agent with the specified modes, mode-choice model and schedule utility.
    pub fn new(
        id: usize,
        modes: Vec<Mode<T>>,
        mode_choice: Option<ChoiceModel<NoUnit<T>>>,
    ) -> Self {
        Agent {
            id,
            modes,
            mode_choice,
        }
    }

    /// Returns an iterator over the modes of the agent.
    pub fn iter_modes(&self) -> impl Iterator<Item = &Mode<T>> {
        self.modes.iter()
    }
}

impl<T: TTFNum> Agent<T> {
    /// Creates an `Agent` from input values.
    ///
    /// Returns an error if some values are invalid.
    pub(crate) fn from_values(
        id: usize,
        alt_choice_type: Option<&str>,
        alt_choice_u: Option<f64>,
        alt_choice_mu: Option<f64>,
        alt_choice_constants: Option<Vec<f64>>,
        alternatives: Option<Vec<Mode<T>>>,
    ) -> Result<Self> {
        let mode_choice = match alt_choice_type {
            Some("First") | None => None,
            Some(ty) => Some(
                ChoiceModel::from_values(
                    Some(ty),
                    alt_choice_u,
                    alt_choice_mu,
                    alt_choice_constants,
                )
                .context("Failed to create choice model")?,
            ),
        };
        let modes =
            alternatives.ok_or_else(|| anyhow!("The agents must have at least one alternative"))?;
        Ok(Agent {
            id,
            modes,
            mode_choice,
        })
    }

    /// Returns an [AgentResult] initialized from the choices made in the pre-day model given
    /// an expected [NetworkSkim] and the results of the previous day (if any).
    ///
    /// If the `update` boolean is `false`, the choices are not computed again. Instead, the
    /// results of the previous day are returned.
    ///
    /// It is an error to call this function with `update = false` and no results for the previous
    /// day.
    #[allow(clippy::too_many_arguments)]
    pub fn make_pre_day_choice(
        &self,
        network: &Network<T>,
        simulation_period: Interval<T>,
        weights: &NetworkWeights<T>,
        exp_skims: &NetworkSkim<T>,
        preprocess_data: &PreprocessingData<T>,
        previous_day_result: Option<&AgentResult<T>>,
        update: bool,
        progress_bar: MetroProgressBar,
        alloc: &mut EAAllocation<T>,
    ) -> Result<AgentResult<T>> {
        if update {
            if let Some(choice_model) = &self.mode_choice {
                // Compute the mode-specific expected utilities and get the callback functions.
                let (expected_utilities, mut callbacks) = itertools::process_results(
                    self.modes.iter().map(|mode| {
                        mode.get_pre_day_choice(
                            network,
                            simulation_period,
                            weights,
                            exp_skims,
                            &preprocess_data.network,
                            progress_bar.clone(),
                        )
                    }),
                    |iter| iter.unzip::<_, _, Vec<_>, Vec<_>>(),
                )
                .with_context(|| {
                    format!(
                        "Failed to compute expected utility for an alternative of agent {}",
                        self.id
                    )
                })?;
                // Get the id of the chosen mode and the global expected utility, from the mode
                // choice model.
                let (choice_id, expected_utility) = choice_model
                    .get_choice(&expected_utilities)
                    .with_context(|| {
                        format!("Failed to select alternative for agent {}", self.id)
                    })?;
                // Call the callback function of the chosen mode to get the mode-specific results.
                let callback = callbacks.swap_remove(choice_id);
                let mode_result = callback(alloc)?;
                Ok(AgentResult::new(
                    self.id,
                    self.modes[choice_id].id(),
                    mode_index(choice_id),
                    expected_utility,
                    mode_result,
                ))
            } else {
                // Choose the first mode.
                let chosen_mode = &self.modes[0];
                let (expected_utility, callback) = chosen_mode.get_pre_day_choice(
                    network,
                    simulation_period,
                    weights,
                    exp_skims,
                    &preprocess_data.network,
                    progress_bar,
                )?;
                let mode_result = callback(alloc)?;
                Ok(AgentResult::new(
                    self.id,
                    self.modes[0].id(),
                    mode_index(0),
                    expected_utility,
                    mode_result,
                ))
            }
        } else if let Some(previous_day_result) = previous_day_result {
            // No update required: simply return the results of the previous day.
            // The results are reset before being returned.
            Ok(previous_day_result.reset())
        } else {
            // No update required but there is no result to return.
            Err(anyhow!("No previous result but `update` is `false`"))
        }
    }
}

impl<T> Index<ModeIndex> for Agent<T> {
    type Output = Mode<T>;
    fn index(&self, index: ModeIndex) -> &Self::Output {
        &self.modes[index.index()]
    }
}

/// Agent identifier.
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct AgentIndex(usize);

impl AgentIndex {
    /// Creates a new AgentIndex.
    pub const fn new(x: usize) -> Self {
        AgentIndex(x)
    }

    /// Returns the index of the AgentIndex.
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Short version of `AgentIndex::new`.
pub const fn agent_index(index: usize) -> AgentIndex {
    AgentIndex::new(index)
}

#[cfg(test)]
mod tests {
    use choice::DeterministicChoiceModel;

    use super::*;
    use crate::mode::{mode_index, ModeResults};
    use crate::units::{Time, Utility};

    fn get_agent() -> Agent<f64> {
        let modes = vec![Mode::Constant((0, Utility(10.)))];
        let choice_model =
            ChoiceModel::Deterministic(DeterministicChoiceModel::new(NoUnit(0.0f64)));
        Agent::new(1, modes, Some(choice_model))
    }

    #[test]
    fn make_pre_day_choice_test() {
        let mut agent = get_agent();
        let network = Network::new(None);
        let mut alloc = EAAllocation::default();
        let bp = MetroProgressBar::new(1);
        assert!(agent
            .make_pre_day_choice(
                &network,
                Interval([Time(0.0), Time(100.0)]),
                &Default::default(),
                &Default::default(),
                &Default::default(),
                None,
                false,
                bp.clone(),
                &mut alloc
            )
            .is_err());

        let result = agent
            .make_pre_day_choice(
                &network,
                Interval([Time(0.0), Time(100.0)]),
                &Default::default(),
                &Default::default(),
                &Default::default(),
                None,
                true,
                bp.clone(),
                &mut alloc,
            )
            .unwrap();
        assert_eq!(result.mode_index, mode_index(0));
        assert_eq!(result.expected_utility, Utility(10.));
        assert_eq!(result.mode_results, ModeResults::None);

        assert_eq!(
            agent
                .make_pre_day_choice(
                    &network,
                    Interval([Time(0.0), Time(100.0)]),
                    &Default::default(),
                    &Default::default(),
                    &Default::default(),
                    Some(&result),
                    false,
                    bp.clone(),
                    &mut alloc,
                )
                .unwrap(),
            result
        );

        agent.modes.push(Mode::Constant((1, Utility(15.))));
        let result = agent
            .make_pre_day_choice(
                &network,
                Interval([Time(0.0), Time(100.0)]),
                &Default::default(),
                &Default::default(),
                &Default::default(),
                None,
                true,
                bp.clone(),
                &mut alloc,
            )
            .unwrap();
        assert_eq!(result.mode_index, mode_index(1));
        assert_eq!(result.expected_utility, Utility(15.));
        assert_eq!(result.mode_results, ModeResults::None);
    }
}
