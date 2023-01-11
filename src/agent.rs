// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

//! Everything related to agents.
use std::ops::Index;

use anyhow::{anyhow, Result};
use choice::ChoiceModel;
use itertools;
use schemars::JsonSchema;
use serde_derive::{Deserialize, Serialize};
use ttf::TTFNum;

use crate::mode::{mode_index, Mode, ModeIndex, PreDayChoiceAllocation};
use crate::network::NetworkSkim;
use crate::schedule_utility::ScheduleUtility;
use crate::simulation::results::PreDayResult;
use crate::simulation::PreprocessingData;
use crate::units::NoUnit;

/// Representation of an independent and intelligent agent that makes one trip per day.
///
/// An agent is characterized by:
///
/// - A set of [modes](Mode) that he/she can take to perform his/her trip.
/// - A [ChoiceModel] describing how his/her mode is chosen, given the expected utilities for each
/// mode.
/// - A [ScheduleUtility] model describing his/her schedule preferences.
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(bound(deserialize = "T: TTFNum"))]
#[schemars(title = "Agent")]
#[schemars(description = "Abstract representation of an individual that makes one trip per day.")]
#[schemars(example = "crate::schema::example_agent")]
pub struct Agent<T> {
    /// Id used when writing the results of the agents.
    #[serde(default)]
    pub id: usize,
    /// Modes accessible to the agent.
    #[validate(length(min = 1))]
    modes: Vec<Mode<T>>,
    /// Choice model used for mode choice.
    ///
    /// When not specified, the first mode is always chosen.
    #[serde(default)]
    mode_choice: Option<ChoiceModel<NoUnit<T>>>,
    /// Schedule-utility preferences.
    #[serde(default)]
    schedule_utility: ScheduleUtility<T>,
}

impl<T> Agent<T> {
    /// Creates a new agent with the specified modes, mode-choice model and schedule utility.
    pub fn new(
        id: usize,
        modes: Vec<Mode<T>>,
        mode_choice: Option<ChoiceModel<NoUnit<T>>>,
        schedule_utility: ScheduleUtility<T>,
    ) -> Self {
        Agent {
            id,
            modes,
            mode_choice,
            schedule_utility,
        }
    }

    /// Returns an iterator over the modes of the agent.
    pub fn iter_modes(&self) -> impl Iterator<Item = &Mode<T>> {
        self.modes.iter()
    }

    /// Returns the schedule-utility preferences of the agent.
    pub const fn schedule_utility(&self) -> &ScheduleUtility<T> {
        &self.schedule_utility
    }
}

impl<T: TTFNum> Agent<T> {
    /// Returns the [PreDayResult] of the agent, i.e., the choices made in the pre-day model given
    /// an expected [NetworkSkim] and the results of the previous day (if any).
    ///
    /// If the `update` boolean is `false`, the choices are not computed again. Instead, the
    /// results of the previous day are returned.
    ///
    /// It is an error to call this function with `update = false` and no results for the previous
    /// day.
    pub fn make_pre_day_choice(
        &self,
        exp_skims: &NetworkSkim<T>,
        preprocess_data: &PreprocessingData<T>,
        previous_pre_day_result: Option<&PreDayResult<T>>,
        update: bool,
        alloc: &mut PreDayChoiceAllocation<T>,
    ) -> Result<PreDayResult<T>> {
        if update {
            if let Some(choice_model) = &self.mode_choice {
                // Compute the mode-specific expected utilities and get the callback functions.
                let (expected_utilities, mut callbacks) = itertools::process_results(
                    self.modes.iter().map(|mode| {
                        mode.make_pre_day_choice(
                            exp_skims,
                            &self.schedule_utility,
                            &preprocess_data.network,
                        )
                    }),
                    |iter| iter.unzip::<_, _, Vec<_>, Vec<_>>(),
                )?;
                // Get the id of the chosen mode and the global expected utility, from the mode choice
                // model.
                let (choice_id, expected_utility) = choice_model.get_choice(&expected_utilities)?;
                // Call the callback function of the chosen mode to get the mode-specific pre-day choices.
                let callback = callbacks.swap_remove(choice_id);
                let mode_result = callback(alloc)?;
                Ok(PreDayResult::new(
                    mode_index(choice_id),
                    expected_utility,
                    mode_result,
                ))
            } else {
                // Choose the first mode.
                let chosen_mode = &self.modes[0];
                let (expected_utility, callback) = chosen_mode.make_pre_day_choice(
                    exp_skims,
                    &self.schedule_utility,
                    &preprocess_data.network,
                )?;
                let mode_result = callback(alloc)?;
                Ok(PreDayResult::new(
                    mode_index(0),
                    expected_utility,
                    mode_result,
                ))
            }
        } else if let Some(previous_pre_day_result) = previous_pre_day_result {
            // No update required: simply return the results of the previous day.
            Ok(previous_pre_day_result.clone())
        } else {
            // No update required but there is no result to return.
            Err(anyhow!(
                "No previous pre-day result but `update` is `false`"
            ))
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
    use crate::mode::mode_index;
    use crate::mode::PreDayChoices;
    use crate::schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel;
    use crate::units::{Time, Utility, ValueOfTime};

    fn get_agent() -> Agent<f64> {
        let modes = vec![Mode::Constant(Utility(10.))];
        let choice_model =
            ChoiceModel::Deterministic(DeterministicChoiceModel::new(NoUnit(0.0f64)));
        let schedule_utility = ScheduleUtility::AlphaBetaGamma(
            AlphaBetaGammaModel::new(
                Time(8. * 60. * 60.),
                Time(8. * 60. * 60.),
                ValueOfTime(5.),
                ValueOfTime(20.),
                true,
            )
            .unwrap(),
        );
        Agent::new(1, modes, Some(choice_model), schedule_utility)
    }

    #[test]
    fn make_pre_day_choice_test() {
        let mut agent = get_agent();
        assert!(agent
            .make_pre_day_choice(
                &Default::default(),
                &Default::default(),
                None,
                false,
                &mut Default::default()
            )
            .is_err());

        let result = agent
            .make_pre_day_choice(
                &Default::default(),
                &Default::default(),
                None,
                true,
                &mut Default::default(),
            )
            .unwrap();
        assert_eq!(result.get_mode_index(), mode_index(0));
        assert_eq!(result.get_expected_utility(), Utility(10.));
        assert_eq!(result.get_choices(), &PreDayChoices::None);

        assert_eq!(
            agent
                .make_pre_day_choice(
                    &Default::default(),
                    &Default::default(),
                    Some(&result),
                    false,
                    &mut Default::default()
                )
                .unwrap(),
            result
        );

        agent.modes.push(Mode::Constant(Utility(15.)));
        let result = agent
            .make_pre_day_choice(
                &Default::default(),
                &Default::default(),
                None,
                true,
                &mut Default::default(),
            )
            .unwrap();
        assert_eq!(result.get_mode_index(), mode_index(1));
        assert_eq!(result.get_expected_utility(), Utility(15.));
        assert_eq!(result.get_choices(), &PreDayChoices::None);
    }
}
