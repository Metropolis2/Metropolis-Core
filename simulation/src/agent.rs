//! Everything related to agents.
use crate::mode::{mode_index, Mode, ModeIndex, PreDayChoiceAllocation};
use crate::network::NetworkSkim;
use crate::schedule_utility::ScheduleUtility;
use crate::simulation::PreDayResult;
use crate::units::NoUnit;

use anyhow::{anyhow, Result};
use choice::ChoiceModel;
use itertools;
use serde_derive::{Deserialize, Serialize};
use std::ops::Index;
use ttf::TTFNum;

/// Representation of an independent and intelligent agent that makes one trip per day.
///
/// An agent is characterized by:
/// - A set of [modes](Mode) that he/she can take to perform his/her trip.
/// - A [ChoiceModel] describing how his/her mode is chosen, given the expected utilities for each
/// mode.
/// - A [ScheduleUtility] model describing his/her schedule preferences.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Agent<T> {
    #[serde(default)]
    pub id: usize,
    /// Modes accessible to the agent.
    modes: Vec<Mode<T>>,
    /// Choice model used for mode choice.
    mode_choice: ChoiceModel<NoUnit<T>>,
    /// Schedule-utility preferences.
    schedule_utility: ScheduleUtility<T>,
}

impl<T> Agent<T> {
    /// Create a new agent with the specified modes, mode-choice model and schedule utility.
    pub fn new(
        id: usize,
        modes: Vec<Mode<T>>,
        mode_choice: ChoiceModel<NoUnit<T>>,
        schedule_utility: ScheduleUtility<T>,
    ) -> Self {
        Agent {
            id,
            modes,
            mode_choice,
            schedule_utility,
        }
    }

    /// Return an iterator over the modes of the agent.
    pub fn iter_modes(&self) -> impl Iterator<Item = &Mode<T>> {
        self.modes.iter()
    }

    /// Return the choice model of the agent for the mode choice.
    pub fn mode_choice(&self) -> &ChoiceModel<NoUnit<T>> {
        &self.mode_choice
    }

    /// Return the schedule-utility preferences of the agent.
    pub fn schedule_utility(&self) -> &ScheduleUtility<T> {
        &self.schedule_utility
    }
}

impl<T: TTFNum> Agent<T> {
    /// Return the [PreDayResult] of the agent, i.e., the choices made in the pre-day model given
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
        previous_pre_day_result: Option<&PreDayResult<T>>,
        update: bool,
        alloc: &mut PreDayChoiceAllocation<T>,
    ) -> Result<PreDayResult<T>> {
        if update {
            // Compute the mode-specific expected utilities and get the callback functions.
            let (expected_utilities, mut callbacks) = itertools::process_results(
                self.modes
                    .iter()
                    .map(|mode| mode.make_pre_day_choice(exp_skims, &self.schedule_utility)),
                |iter| iter.unzip::<_, _, Vec<_>, Vec<_>>(),
            )?;
            // Get the id of the chosen mode and the global expected utility, from the mode choice
            // model.
            let (choice_id, expected_utility) = self.mode_choice.get_choice(&expected_utilities)?;
            // Call the callback function of the chosen mode to get the mode-specific pre-day choices.
            let callback = callbacks.swap_remove(choice_id);
            let mode_result = callback(alloc)?;
            Ok(PreDayResult::new(
                mode_index(choice_id),
                expected_utility,
                mode_result,
            ))
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
    pub fn new(x: usize) -> Self {
        AgentIndex(x)
    }

    pub fn index(self) -> usize {
        self.0
    }
}

/// Short version of `AgentIndex::new`.
pub fn agent_index(index: usize) -> AgentIndex {
    AgentIndex::new(index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mode::mode_index;
    use crate::mode::PreDayChoices;
    use crate::schedule_utility::alpha_beta_gamma::AlphaBetaGammaModel;
    use crate::units::{Time, Utility, ValueOfTime};
    use choice::DeterministicChoiceModel;

    fn get_agent() -> Agent<f64> {
        let modes = vec![Mode::Constant(Utility(10.))];
        let choice_model =
            ChoiceModel::Deterministic(DeterministicChoiceModel::new(NoUnit(0.0f64)).unwrap());
        let schedule_utility = ScheduleUtility::AlphaBetaGamma(AlphaBetaGammaModel::new(
            Time(8. * 60. * 60.),
            Time(8. * 60. * 60.),
            ValueOfTime(5.),
            ValueOfTime(20.),
            true,
        ));
        Agent::new(1, modes, choice_model, schedule_utility)
    }

    #[test]
    fn make_pre_day_choice_test() {
        let mut agent = get_agent();
        assert!(agent
            .make_pre_day_choice(&Default::default(), None, false, &mut Default::default())
            .is_err());

        let result = agent
            .make_pre_day_choice(&Default::default(), None, true, &mut Default::default())
            .unwrap();
        assert_eq!(result.get_mode_index(), mode_index(0));
        assert_eq!(result.get_expected_utility(), Utility(10.));
        assert_eq!(result.get_choices(), &PreDayChoices::None);

        assert_eq!(
            agent
                .make_pre_day_choice(
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
            .make_pre_day_choice(&Default::default(), None, true, &mut Default::default())
            .unwrap();
        assert_eq!(result.get_mode_index(), mode_index(1));
        assert_eq!(result.get_expected_utility(), Utility(15.));
        assert_eq!(result.get_choices(), &PreDayChoices::None);
    }
}
