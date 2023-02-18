# Agent Results

For each agent, Metropolis gives as output:

- `id`: The id of the agent given in the input (for convenience).
- `mode`: The index of the mode chosen, for the last iteration (indices start at 0, so index 2 is the third
  mode in the agent's input values).
- `expected_utility`: The expected utility resulting from the mode-choice model, for the last iteration.
- `mode_results`: Additional results specific to the mode chosen.

## Constant-Utility Modes

For modes that yield a constant utility level, there is no additional result stored.

## Trip Modes

For trip modes, the following additional results are stored:

- `departure_time`: The departure time from the origin of the first leg (before the origin delay
  time).
- `arrival_time`: The arrival time at the destination of the last leg (after the last stopping
  time).
- `total_travel_time`: The total time spent traveling.
- `utility`: The (deterministic) utility resulting from the trip.
- `expected_utility`: The utility expected from the trip before starting it.
- `virtual_only`: Boolean indicating if the trip is compose of virtual legs only.
- `legs`: Additional results specific to each leg of the trip.

### Leg-Specific Results

For each leg of a trip, the following results are stored:

- `departure_time`: The departure time from the origin of the leg.
- `arrival_time`: The arrival time at the destination of the leg (before the stopping time).
- `travel_utility`: The travel utility resulting from this leg.
- `schedule_utility`: The schedule utility resulting from this leg.

For road legs, the following additional results are stored:

- `route`: List of edges taken, with the entry time of each edge.
- `road_time`: Total time spent traveling on an edge.
- `in_bottleneck_time`: Total time spent at the entry bottleneck of an edge.
- `out_bottleneck_time`: Total time spent at the exit bottleneck of an edge.
- `route_free_flow_travel_time`: Travel time when taking the same route assuming no congestion.
- `global_free_flow_travel_time`: Travel time of the fastest no-congestion route between the origin
  and the destination of the leg.
- `length`: Length of the route taken.
- `pre_exp_departure_time`: Expected departure time from the origin of the leg, in the pre-day
  model.
- `pre_exp_arrival_time`: Expected arrival time at the destination of the leg (before the stopping
  time), in the pre-day model.
- `exp_arrival_time`: Expected arrival time at the destination of the leg (before the stopping
  time), when leaving origin.
