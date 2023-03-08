# Congestion and spillback modeling

**Table of Contents**

<!-- toc -->

An edge of the road network is composed of three parts:

- An **entry bottleneck** (or **in bottleneck**) that limits the flow of vehicle entering the edge.
- A **running part** where the vehicles travel at a speed given by a speed-density function.
- An **exit bottleneck** (or **out bottleneck**) that limits the flow of vehicle exiting the edge.

These three components are presented in more details in the following sections.

## Vehicle types

Each vehicle type of a road network is characterized by:

- A **headway**: length between the head of the vehicle and the head of the following vehicle
  (headway should be given under traffic jam or low speed conditions).
- A **passenger-car equivalent** **(PCE)**: weight of the vehicle compared to a standard
  passenger car, in bottleneck scenarios.
- A **speed function**: vehicle speed as a function of the speed for the base vehicle.
- **Allowed edges**: list of edges that the vehicle _can_ take (all edges are allowed if empty).
- **Restricted edges**: list of edges that the vehicle _cannot_ take (all edges are allowed if empty).

## Exit bottleneck

### Definition

Each edge of the road network has an exit bottleneck with a flow \\( s^o \\), expressed in PCE per
second.
The value \\( s^o \\) is called the **output flow** of the edge.
When not specified, the output flow is \\( s^o = \infty \\), i.e., there is no restriction to the
flow of vehicles that can exit the edge.

When the output flow is finite, i.e., \\( s^o < \infty \\), then each time a vehicle with a PCE
\\( v^{PCE} \\) exits the edge, the exit bottleneck is closed for a duration of
\\( v^{PCE} / s^o \\) seconds.
For example, if the output flow is \\( s^o = 0.5 \\) PCE / second, and a standard passenger car (\\(
v^{PCE} = 1 \\)) exits the edge, then the exit bottleneck gets closed for 2 seconds.
Therefore, with an output flow of \\( s^o = 0.5 \\), there can at most be 1800 PCE vehicles exiting
the edge in a hour.
The value \\( 3600 \cdot s^o \\) is usually called the **output capacity** of the edge.

### Simulation

When the within-day model starts, a `BottleneckState` is created for each edge of the road network
with a finite output flow.
The `BottleneckState` holds the timing of the next opening of the bottleneck (by default set to
`0.0`) and a queue of vehicles waiting at the bottleneck (empty by default).

Additionnally, events `BottleneckEvent` are used to simulate the opening of a bottleneck.
A `BottleneckEvent` holds the execution time of the event (i.e., the opening time of the
bottleneck), the index of the edge the bottleneck belongs to and an indicator for entry or exit
bottleneck.

Assume that a vehicle \\( v \\) with PCE \\( v^{PCE} \\) reaches the end of an edge with output flow
\\( s^o \\) at time \\( t \\).

- If \\( t \\) is later than the bottleneck's next opening, it means that the bottleneck is open.
  Then, the vehicle exits the edge and the next opening is set to \\( t + v^{PCE} / s^o \\).
- If \\( t \\) is earlier than the bottleneck's next opening and the bottleneck queue is empty, it
  means that the bottleneck is closed and an event needs to be created. Then, a `BottleneckEvent` is
  created with an execution time set to the bottleneck's next opening. The vehicle \\( v \\) is
  inserted in the bottleneck queue. The next opening time is increased by \\( v^{PCE} / s^o \\).
- If \\( t \\) is earlier than the bottleneck's next opening and the bottleneck queue is non-empty,
  it means that the bottleneck is closed and an event has been created to let the next vehicle pass
  when it opens again. Then, the vehicle \\( v \\) is pushed to the end of the bottleneck queue.
  The next opening time is increased by \\( v^{PCE} / s^o \\).

When a `BottleneckEvent` is executed at time \\( t \\), the next vehicle in the bottleneck queue is
allowed to exit the edge.
The next opening time of the bottleneck is set to \\( t + v^{PCE} / s^o \\).
If the queue is not empty, the `BottleneckEvent` is set to execute again at time
\\( t + v^{PCE} / s^o \\).

> Note. For edges with an infinite output flow, the simulator behaves like if the exit bottleneck is
> always open.

### Recording

The within-day model needs to record the observed waiting times as a function of the entry times in
the bottleneck.
Therefore, a piecewise-linear time function is built with a period and an interval length defined by
the parameters `period` and `recording_interval` (see
[Representing travel-time functions](../getting_started/ttf.md) for more details).

A point of the piecewise-linear time function represents the average waiting time observed during
the time interval.
For example, if the `recording_interval` parameter is set to 10 minutes, the point at time
`08:00:00` represents the average waiting time between `07:55:00` and `08:05:00`.
The average is computed with the weighted average of observed waiting time, where the weights
correspond to the time during which the given waiting time was observed.

The waiting time is zero at the beggining of the period and it changes each time a vehicle exits the
bottleneck or the queue gets empty (i.e., the last vehicle in the queue exits the bottleneck through
a `BottleneckEvent`).

> Note. If a single vehicle crosses the bottleneck during the recording period, at time \\( t \\).
> Then, the recorded waiting time will be of zero during the whole period, even though a vehicle
> arriving at the bottleneck during the time interval \\( [t, t + v^{PCE} / s^o] \\) would face some
> waiting time. This is done on purpose. It means that if the same vehicle were to arrive at the
> bottleneck at about the same time on the next day, it would not anticipate some waiting time just
> because it generated some waiting time itself the day before.
>
> In a way, the waiting times recorded are assuming that there is 1 less vehicle in the queue, so
> that vehicles to not anticipate the waiting times generated by themselves, making the simulations
> more stable.
