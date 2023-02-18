# Agents

An agent is an autonomous entity that can make trips.

**Table of Contents**

<!-- toc -->

## JSON representation

Each agent is represented in JSON as an Object with three fields:

- `id` (integer, optional): identifier of the agent (default is 0)
- `mode_choice` (`ChoiceModel`, optional): model describing how the agent chooses a mode (default is
  to choose the first mode in the `modes` list)
- `modes` (Array of `Mode`): modes available to the agent

The `id` is reported in the agent results, allowing to match an agent result with an input agent
(this is just for convenience, the agent results should be sorted in the same order as the input
agents).
It is _not_ required that the ids are unique.

Each agent must have at least one mode available.

### Choice Model

There are two types of choice models:

- **Deterministic:** The alternative with the largest utility is chosen.
- **Logit:** The alternative is chosen using Multinomial Logit probabilities.

#### Deterministic choice model

A deterministic choice model has one parameter: `u`, a `float` between `0.0` and `1.0`.
This parameter is only used when there are two or more alternatives with the exact same value.
If there are two such alternatives, the first one is chosen if `u <= 0.5`; the second one is chosen
otherwise.
If there are three such alternatives, the first one is chosen is `u <= 0.33`; the second one is
chosen if `0.33 < u <= 0.67`; and the third one is chosen otherwise.
And so on for 4 or more alternatives.

An example JSON representation of a deterministic choice model is

```json
{
  "type": "Deterministic",
  "value": {
    "u": 0.4
  }
}
```

#### Logit choice model

A Logit choice model has two parameters:

- `u` (`float` between `0.0` and `1.0`)
- `mu` (`float` greater than or equal to `0.0001`)

The parameter `mu` represents the variance of the extreme-value distributed random terms in the
Logit theory.

The parameter `u` indicates how the alternative is chosen from the Logit probabilities (See [Inverse
transform sampling](https://en.wikipedia.org/wiki/Inverse_transform_sampling)).

An example JSON representation of a Logit choice model is

```json
{
  "type": "Logit",
  "value": {
    "u": 0.4,
    "mu": 2.0
  }
}
```

### Modes

The current version of Metropolis support two different types of modes:

- **Constant:** An activity that always yields the same amount of utility.
- **Trip:** A trip composed of one or more legs (road or virtual).

#### Constant mode

A constant mode takes only one value: a `float` representing the utility that the agent gets when
choosing this mode.

An example JSON representation of a Constant mode is

```json
{
  "type": "Constant",
  "value": 1.0
}
```

#### Trip mode

See [Representing trips](trips.md).

An example JSON representation of a Trip mode, with only one virtual leg with 1-minute travel time,
is

```json
{
  "type": "Trip",
  "value": {
    "legs": [
      {
        "class": {
          "type": "Virtual",
          "value": 60.0
        }
      }
    ],
    "departure_time_model": {
      "type": "Constant",
      "value": 0.0
    }
  }
}
```

### Example

Below is an example of agent that can choose, using Logit probabilities, between a mode that
provides a constant utility of 0 and a 1-leg trip on the road.
The trip is from origin 0 to destination 1, with vehicle 0.
It has a fixed departure time of 100 seconds after midnight, with utility equal to
`u(tt) = -0.01 * tt`, where `tt` is the travel time.

```json
{
  "id": 1,
  "mode_choice": {
    "type": "Logit",
    "value": {
      "u": 0.5,
      "mu": 1.0
    }
  },
  "modes": [
    {
      "type": "Constant",
      "value": 0.0
    },
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
            }
          }
        ],
        "departure_time_model": {
          "type": "Constant",
          "value": 100.0
        },
        "total_travel_utility": {
          "type": "Polynomial",
          "value": {
            "b": -0.01
          }
        }
      }
    }
  ]
}
```
