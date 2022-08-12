use crate::{ChoiceModel, DeterministicChoiceModel};

pub fn example_choice_model() -> ChoiceModel<f64> {
    ChoiceModel::Deterministic(DeterministicChoiceModel::new(0.5))
}
