# Representing travel-time functions

**Table of Contents**

<!-- toc -->

Metropolis makes heavy use a travel-time functions (e.g., when representing an edge's weight or a
travel-time function for an origin-destination pair).
A travel-time function (*TTF* for short) is a function \\(f: t \mapsto f(t)\\), which gives for any departure time
\\(t \in [t_0, t_1]\\) a travel time \\(f(t)\\), where \\([t_0, t_1]\\) is called the departure-time
period.
For any departure time outside of the departure-time period, the travel time is assumed to be
infinite.

In Metropolis, departure time is always expressed in number of seconds since midnight and travel
time is expressed in number of seconds.
For example, the value `36062.3` can be decomposed as `10 * 60 * 60 + 1 * 60 + 2 + 0.3` so it can
represent, depending on context, a departure time of `10:01:02.3` or a travel time of 10 hours, 1
minute, 2 seconds and 300 milliseconds.

## Internal representation

Internally, travel-time functions are represented as a value that can take two types: a **constant
value** or a **piecewise-linear function**.

### TTF as a constant value

When a TTF is represented as a constant value \\(c\\), it means that the TTF is a constant function
\\(f: t \mapsto c\\).
In this case, the departure-time period is always assumed to be \\((-\infty, +\infty)\\) (i.e., any
departure time is possible).

### TTF as a piecewise-linear function

Any piecewise-linear function \\(f: x \mapsto f(x)\\) can be represented as a list of breakpoints
\\([(x_0, y_0), \dots, (x_n, y_n)]\\), where the value \\(f(x)\\) for any \\(x \in [x_i, x_{i+1})\\)
is given by the linear interpolation between the points \\((x_i, y_i)\\) and \\((x_{i+1},
y_{i+1})\\).

In Metropolis, since version `0.3.0`, the \\( x_i \\) values must always be evenly spaced and thus,
a piecewise-linear function can be represented by three components:

- A vector with the values \\( [y_0, \dots, y_n] \\).
- The period start \\( x_0 \\).
- The spacing between \\( x \\) values, i.e., the value \\( \delta x \\) such that \\( \delta x =
  x_{i+1} - x_i, \\: \forall i \in [1, n - 1] \\).

The spacing \\( \delta x \\) between \\( x \\) values is set by the road-network parameter
`recording_interval`.
The period start, \\( x_0 \\), and the period end, \\( x_0 + n \cdot \delta x \\),  are set by the
simulation parameter `period`.

> WARNING. When an user gives piecewise-linear breakpoint functions as input (for example, in the
> JSON file with the road-network weights), the functions must have all (i) the same number of
> \\( y \\) values, (ii) the same period start \\( x_0 \\) and (iii) the same spacing
> \\( \delta x \\). The simulator does not check that these rules are satisfied but unspecified
> behavior can occur if they are not.

<!-- TODO: Add a graph -->


## Travel-time functions in JSON files

Travel-time functions appear multiple time in the input and output JSON files of Metropolis so it is
important to understand how they are written as JSON data.

To represent a constant TTF, you simply need to give the constant travel time (in number of seconds)
as a float.
For example, a travel time of 90 seconds can be represented as

```json
90.0
```

To represent a piecewise-linear TTF, you need to give an Object with three fields

- `points`: an Array of float representing the \\( y \\) values (in seconds)
- `start_x`: a float representing the period start \\( x_0 \\) (in seconds)
- `interval_x`: a float representing the spacing between \\( x \\) values (in seconds)

For example, the following input

```json
{
  "points": [10.0, 20.0, 16.0],
  "start_x": 10.0,
  "interval_x": 10.0
}
```
represents a piecewise-linear TTF where the travel time is

- Infinity for departure time `00:00:09` (infinity before the start of the period),
- 10 seconds for departure time `00:00:10`,
- 11 seconds for departure time `00:00:11` (interpolation between 10 and 20),
- 20 seconds for departure time `00:00:20`,
- 18 seconds for departure time `00:00:25` (interpolation between 20 and 10),
- 16 seconds for departure time `00:00:30`,
- 16 seconds for departure time `00:00:35` (equal to last breakpoint for a departure time later than
  the last breakpoint).

<!-- TODO: add a graph -->
