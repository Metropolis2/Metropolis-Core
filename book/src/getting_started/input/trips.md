# Trips

In Metropolis, a trip is a sequence of one or more leg.
The trip consists in traveling sequentially through all the legs, in the given order.

**Table of Contents**

<!-- toc -->

## Leg

There are two different classes of legs:

- **Road**: The leg consists in a trip on the road network of the simulation, between a given origin
  and destination, with a given vehicle type.
- **Virtual**: The leg does not happen on the road network and has an exogenous travel time (that can
  optionally be time-dependent).

## Timings

The timings of a trip are as follows:

- Given the departure time of the trip, the first leg starts after the given **origin delay** has
  elapsed.
- When a leg starts, the agent immediately enters the road network at origin (for road legs) or
  wait for the given travel time (for virtual legs).
- As soon as the agent reaches the destination of the leg (for road legs) or waited for the given
  travel time (for virtual legs), the agent waits for the given **stopping time** of the leg then
  starts the next leg (if any).

To understand how schedule utility is computed, it is important to understand how departure times
and arrival times are defined:

- The *departure time of the trip* is defined as the time at which the origin delay starts.
- The *departure time of a leg* is defined as the time at which leg starts (i.e., end of the origin
  delay for the first leg and end of the stopping time of the previous leg for all the other legs).
- The *arrival time of a leg* is defined as the time at which the stopping time of the leg starts.
- The *arrival time of the trip* is defined as the time at which the stopping time of the last leg
  elapsed.

## Trip utility

The total utility of a trip is the sum of five components:

- The *schedule utility at origin*, a function of the departure time of the trip.
- The *schedule utility at destination*, a function of the arrival time of the trip.
- The *total travel utility*, a function of the sum of the travel time for each leg of the trip.
- The *schedule utility of each leg*, a function of the arrival time of each leg.
- The *travel utility of each leg*, a function of the travel time of each leg.

## JSON representation

A `Trip` is composed of five parameters:

- `legs` (Array of `Leg`): The legs of the trip, in the order of execution. The Array must have at
  least one element.
- `departure_time_model` (`DepartureTimeModel`): Model describing how the departure time of the trip
  is elected.
- `origin_delay` (`float`, optional): Time in seconds spent waiting between the starting time of the
  trip and the start of the first leg (e.g., to represent the time needed to start the car and leave
  the parking). Default is 0.0.
- `total_travel_utility` (`TravelUtility`, optional): Representation of a 1-variable function
  describing how the total travel utility is computed, as a function of the total travel time of the
  trip. Default is a constant utility of 0.0.
- `origin_schedule_utility` (`ScheduleUtility`, optional): Representation of a 1-variable function
  describing how the schedule utility at origin is computed, as a function of the trip departure
  time. Default is a constant utility of 0.0.
- `destination_schedule_utility` (`ScheduleUtility`, optional): Representation of a 1-variable
  function describing how the schedule utility at destination is computed, as a function of the trip
  arrival time. Default is a constant utility of 0.0.

### Leg

A `Leg` is composed of four values:

- `class` (`LegType`): The type of the leg (road or virtual).
- `stopping_time` (`float`, optional): Stopping time in seconds at the end of the leg. Default is 0.
- `travel_utility` (`TravelUtility`, optional): Travel-utility function describing how the travel
  utility of the leg is computed, given the leg's travel time. Default is a constant utility of 0.0.
- `schedule_utility` (`ScheduleUtility`, optional): Schedule-utility function describing how the
  schedule utility of the leg is computed, given the leg's travel time. Default is a constant
  utility of 0.0.

There are two kinds of `LegType`:

- **Virtual**: A virtual leg with a travel-time function given as a `TTF` (See [Representing
  travel-time functions](../ttf.md)).
- **Road**: A road leg with a given origin (`integer`), destination (`integer`) and vehicle type
  (`integer`).

The road-leg's origins and destinations must be the index of the origin / destination node.
The vehicle value must be the index of the vehicle type.

An example of a virtual leg, with a 1-minute travel time and 5 seconds of stopping time, is

```json
{
  "class": {
    "type": "Virtual",
    "value": 60.0
  },
  "stopping_time": 5.0
}
```

An example of a road leg, from origin 0 to destination 1 with vehicle index 0, is

```json
{
  "class": {
    "type": "Road",
    "value": {
      "origin": 0,
      "destination": 1,
      "vehicle": 0
    }
  }
}
```

> Note. The origin of a leg does not have to be equal to the destination of the previous leg and the
> vehicle type of a leg does not have to be equal to the vehicle type of the previous leg, i.e.,
> agents can "teleport" and switch vehicles.

### Departure-time model

A departure-time model describes how the departure time of the trip is elected.

There are two types of departure-time model:

- **Constant**: The departure time is always set to the given value.
- **ContinuousChoice**: The departure time is chosen at each iteration using the Continuous Logit
  model.

For a **Constant** departure-time model, use the following representation:

```json
{
  "type": "Constant",
  "value": 18000.0
}
```

where the given value represents the departure time, in seconds after midnight.

For a **ContinuousChoice** departure-time model, use the following representation:

```json
{
  "type": "ContinuousChoice",
  "value": {
    "period": [18000.0, 36000.0],
    "choice_model": {
      "type": "Logit",
      "value": {
        "u": 0.5,
        "mu": 1.0
      }
    }
  }
}
```

where `period` is an Array with two elements representing the start and end of the period in which
the departure time is chosen and `choice_model` is an Object with two values, `type` and `value`.
The value `type` must be always equal to `"Logit"`.
The value `value` must be an Object with two values:

- `u` (`float` between `0.0` and `1.0`)
- `mu` (`float` greater than or equal to `0.0001`)

The parameter `mu` represents the variance of the extreme-value distributed random terms in the
Continuous Logit theory.

The parameter `u` indicates how the alternative is chosen from the Logit probabilities (See [Inverse
transform sampling](https://en.wikipedia.org/wiki/Inverse_transform_sampling)).

### Travel utility

A `TravelUtility` is an Object representing a function that yields a utility level given a travel
time.

Currently, there is only one type of travel-utility function supported: a polynomial function of
degree 4.
Constant, linear, quadratic and cubic functions can be represented by setting the higher-order
coefficients to zero.

To represent a polynomial function, use the following Object:

```json
{
  "type": "Polynomial",
  "value": {
    "a": 2.0,
    "b": -1.0,
    "c": 0.5,
    "d": -0.5,
    "e": 0.1
  }
}
```

The parameters `a`, `b`, `c`, `d` and `e` represent the polynomial coefficient of degree 0, 1, 2, 3
and 4 respectively.
Therefore, the following example represent the function
`f(x) = 2 - x + 0.5 * x^2 - 0.5 * x^3 + 0.1 * x^4`.
All parameters are optional with a default value of 0.

### Schedule utility

A `ScheduleUtility` is an Object representing a function that yields a utility level given a
departure or arrival time.

Currently, there are two types of schedule-utility function:

- **None**: The utility is always zero.
- **AlphaBetaGamma**: The utility is computed using Arnott, de Palma, Lindsey's alpha-beta-gamma
  model.

**None** is the default so if the `ScheduleUtility` is not specified, it is assumed to be zero.
To represent a `ScheduleUtility` of type **None**, use

```json
{
  "type": "None"
}
```

For **AlphaBetaGamma**, there are four parameters:

- `t_star_low` (`float`): the earliest desired departure or arrival time, in seconds after midnight
- `t_star_high` (`float`): the latest desired departure or arrival time, in seconds after midnight
  (must not be smaller than
  `t_star_low`)
- `beta` (`float`): the penalty for early departure or arrival, in utility per second
- `gamma` (`float`): the penalty for late departure or arrival, in utility per second

Given a departure or arrival time `t`, the schedule utility is (note the minus to convert from cost
to utility):

- `-beta * (t_star_low - t)` if `t < t_star_low`
- `-gamma * (t - t_star_high)` if `t > t_star_high`
- `0` otherwise

The following example represents an **AlphaBetaGamma** function with `t* = 08:00AM`,
`beta = 9 €/h` and `gamma = 27 €/h`.

```json
{
  "type": "AlphaBetaGamma",
  "value": {
    "t_star_low": 28800.0,
    "t_star_high": 28800.0,
    "beta": 0.0025,
    "gamma": 0.0075
  }
}
```

### Example

Below is an example of trip from origin 0 to destination 2, with an intermediate stop at node 1 of 5
minutes.
All the trip takes place with the vehicle type of index 0.
The trip starts at time 00:00AM.
The trip utility is a linear function of the total travel time.

```json
{
  "type": "Trip",
  "value": {
    "legs": [
      {
        "class": {
          "type": "Road",
          "value": {
            "origin": 0,
            "destination": 1,
            "vehicle": 0
          }
        },
        "stopping_time": 300.0,
      },
      {
        "class": {
          "type": "Road",
          "value": {
            "origin": 1,
            "destination": 2,
            "vehicle": 0
          }
        }
      }
    ],
    "departure_time_model": {
      "type": "Constant",
      "value": 0.0
    },
    "total_travel_utility": {
      "type": "Polynomial",
      "value": {
        "b": -0.005
      }
    }
  }
}
```
