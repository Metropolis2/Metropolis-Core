use crate::{ChoiceModel, DeterministicChoiceModel};

pub(crate) fn example_choice_model() -> ChoiceModel<f64> {
    ChoiceModel::Deterministic(DeterministicChoiceModel::new(0.5))
}
