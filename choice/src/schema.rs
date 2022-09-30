// Copyright 2022 Lucas Javaudin
//
// Licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International
// https://creativecommons.org/licenses/by-nc-nd/4.0/legalcode

use crate::{ChoiceModel, DeterministicChoiceModel};

pub(crate) fn example_choice_model() -> ChoiceModel<f64> {
    ChoiceModel::Deterministic(DeterministicChoiceModel::new(0.5))
}
