# Representing travel-time functions

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

A TTF can be represented as a list of breakpoints \\([(x_0, y_0), \dots, (x_n, y_n)]\\), together
with the departure-time period \\([t_0, t_1]\\), where the following properties must always hold:

- The departure time at the first breakpoint is equal to the start of the departure-time period,
  i.e., \\( x_0 = t_0 \\).
- The departure time at the last breakpoint is not larger than the end of the departure-time period,
  i.e., \\( x_n \le t_1 \\).
- The departure-time breakpoints \\( [x_0, \dots, x_n] \\) are sorted in increasing order.

> WARNING. In the current version, when an user gives a piecewise-linear breakpoint function as an
> input in a JSON file, the properties above are not checked. It is the user's responsibility to
> ensure that they are verified.

Then, the TTF has the following properties:

- For any departure time breakpoint \\( x_i \\), the corresponding travel time is \\( y_i \\).
- For any departure time \\( x \\), such that \\( x \in (x_i, x_{i+1}) \\), the corresponding travel
  time is given by the linear interpolation between the points \\( (x_i, y_i) \\) and
  \\( (x_{i+1}, y_{i+1}) \\).
- For any departure time \\( x \\), such that \\( x < t_0 \\), the travel time is infinite.
- For any departure time \\( x \\), such that \\( x > t_1 \\), the travel time is infinite.
- For any departure time \\( x \\), such that \\( x_n < x \le t_1 \\), the travel time is
  \\( y_n \\).

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

To represent a piecewise-linear TTF, you need to give an Object with two fields

- `points`: an Array of 2-value Arrays representing the list of breakpoints
- `period`: a 2-value Array representing the departure-time period

For example, the following input

```json
{
  "points": [
    [10.0, 10.0],
    [20.0, 20.0],
    [30.0, 16.0]
  ],
  "period": [10.0, 40.0]
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
  the last breakpoint),
- 16 seconds for departure time `00:00:40` (equal to last breakpoint for a departure time later than
  the last breakpoint),
- Infinity for departure time `00:00:41` (infinity after the end of the period).

> NOTE. When serialized (i.e., in the output files), the piecewise-linear TTFs have two additional
> fields `min` and `max` with the minimum and maximum travel time value of the function.
> These two fields are ignored when deserializing (i.e., in the input files).

<!-- TODO: add a graph -->

## Travel-time function simplifications

At many different points in the code, the travel-time functions are simplified by removing some
breakpoints.
This is done to reduce the memory size and computation time of working with complex travel-time
functions.

There are three kinds of simplifications.

1. **Raw simplification**: Only the unneeded breakpoints are removed. A breakpoint is unneeded if
   removing it does not change the function (i.e., the breakpoint is exactly on the straight line
   between the previous and the next breakpoint).
2. **Bounded simplification**: Removing as many breakpoints as possible, while satisfying the constraint
   that the maximum absolute difference between the original function and the new function is
   smaller than the given bound (expressed in seconds). The simplification is done using
   Reumann-Witkam simplification.
 3. **Interval simplification**: Construct a new function by evaluating the original function at
   fixed time interval. For example, if the original TTF has a period of `08:00:00` to `08:35:00`
   and we simplify it with an interval of 15 minutes, the resulting TTF will be a TTF with
   breakpoints at time `08:00:00`, `08:15:00` and `08:30:00`. Note that any unneeded breakpoint is
   removed so the `08:15:00` breakpoint could be removed if it lies on the straight line between the
   `08:00:00` and the `08:30:00` breakpoints.

> Note. When simplifying a TTF represented as a constant value, nothing is done (even with interval
> simplification).

### JSON representation

You can choose how TTFs are simplified as parameters of the model.
Anytime the input require is of type `TTFSimplification`, you can use one of the three
representations presented below.

For **Raw simplification**, simply use a string:
```json
"Raw"
```

For **Bounded simplification**, use the following Object:
```json
{
  "type": "Bounded",
  "value": 1.0
}
```
where the value represents the maximum bound of travel-time difference between the original and the
new function, in seconds.

For **Interval simplification**, use the following Object:
```json
{
  "type": "Interval",
  "value": 300.0
}
```
where the value represents the (fixed) time interval between two breakpoints, in seconds.

> Note. The default `TTFSimplification` value is `"Raw"`.
