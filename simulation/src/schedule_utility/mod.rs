use crate::units::{Time, Utility};
use alpha_beta_gamma::AlphaBetaGammaModel;

use serde_derive::{Deserialize, Serialize};
use ttf::{TTFNum, TTF};

pub mod alpha_beta_gamma;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum ScheduleUtility<T> {
    AlphaBetaGamma(AlphaBetaGammaModel<T>),
}

impl<T: TTFNum> ScheduleUtility<T> {
    /// Return a vector of breakpoints (departure time, travel time) that should be added to the
    /// travel-time function before computing the utility to ensure that the linear interpolation
    /// assumption is good enough.
    ///
    /// The breakpoints must be order by increasing departure time.
    pub fn get_breakpoints(&self, ttf: &TTF<Time<T>>) -> Vec<(Time<T>, Time<T>)> {
        match self {
            Self::AlphaBetaGamma(model) => model.get_breakpoints(ttf),
        }
    }

    pub fn get_utility(&self, departure_time: Time<T>, arrival_time: Time<T>) -> Utility<T> {
        match self {
            Self::AlphaBetaGamma(model) => model.get_utility(departure_time, arrival_time),
        }
    }
}
