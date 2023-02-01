# Routing queries

The file `compute_travel_times` is a standalone executable that ships with every version of
Metropolis.
It can be used to run efficiently many time-dependent routing queries on a graph.
Internally, it uses the same algorithms as Metropolis.

**Table of Contents**

<!-- toc -->

## Terminology

### Graph

- **Static graph** A graph where all edges' weights (which usually represent travel times) are
  constant.
- **Time-dependent graph** A graph where some (or all) edges' weights are functions \\(f(t)\\) that
  yields the travel time on the edge for any time \\(t\\).

### Query source / target variants

- **Point-to-point query** Shortest path from a node \\(u\\) to a node \\(v\\).
- **Single-source (or single-target) query** Shortest paths from a node \\(u\\) to all other nodes
  of the graph (in reverse for single-target queries).
- **All-to-all query** Shortest paths from any node \\(u\\) to any node \\(v\\) of the graph.
- **One-to-many (or many-to-one) query** Shortest paths from a node \\(u\\) to all other nodes in a
  set \\(T\\) of target nodes (in reverse for many-to-one queries).
- **Many-to-many query** Shortest paths from a set \\(S\\) of source nodes to a set \\(T\\) of
  target nodes.

### Query objective function variants

- **Static query** In a graph with constant edge weights, query \\(S(s, t)\\) that returns the
  minimum travel time between a source node \\(s\\) and a target node \\(t\\).
- **Earliest-arrival query** In a time-dependent graph, query \\(EA(s, t, \tau_0)\\) that returns
  the earliest possible arrival at a target node \\(t\\), when leaving from a source node \\(s\\)
  at time \\(\tau_0\\).
- **Travel-time profile query** In a time-dependent graph, query \\(TTP(s, t)\\) that returns a
  function \\(f(\tau)\\) that yields the minimum travel-time, from source \\(s\\) to target \\(t\\),
  given any possible departure time \\(\tau\\).
- **Multicriteria query** When the cost function maximizes multiple criteria, query that returns a
  Pareto set of shortest paths, from source to target.


## Getting Started

The help message of the command explains how to run the command and set the input and output file
paths.

To print the help message, use

```shell
$ ./compute_travel_times --help
Compute efficiently earliest-arrival or profile queries

Usage: compute_travel_times [OPTIONS] --queries <QUERIES> --graph <GRAPH> --result <RESULT>

Options:
      --queries <QUERIES>
          Path to the file where the queries to compute are stored

      --graph <GRAPH>
          Path to the file where the graph is stored

      --weights <WEIGHTS>
          Path to the file where the graph weights are stored. If not specified, the weights are read from the graph file (with key "weight")

      --parameters <PARAMETERS>
          Path to the file where the parameters are stored

      --result <RESULT>
          Path to the file where the results of the queries should be stored

      --input-order <INPUT_ORDER>
          Path to the file where the node ordering is stored (only for intersect and tch). If not specified, the node ordering is computing automatically

      --output-order <OUTPUT_ORDER>
          Path to the file where the node ordering should be stored (only for intersect and tch). If not specified, the node ordering is not saved

      --output-overlay <OUTPUT_OVERLAY>
          Path to the file where the hierarchy overlay should be stored (only for intersect and tch). If not specified, the hierarchy overlay is not saved

  -h, --help
          Print help (see a summary with '-h')

  -V, --version
          Print version
```

The command takes as input 5 JSON files (3 of them are optional).

- **Graph file** which contains a description of the graph to use as input
- **Queries file** which contains the queries (earliest-arrival or profile) to execute
- **Weights file** (optional) which contains the edges' weights to use as input (if not specified,
  the weights are read from the graph file)
- **Parameters file** (optional) which contains the parameters of the algorithm to run
- **Node order file** (optional) which contains the node order to use for pre-processing (useful to
  speed-up the pre-processing part of the contraction hierarchy when using the same graph multiple
  times)

The command yields as output 3 JSON files (2 of them are optional).

- **Output file** which contains the results of the queries and other secondary results
- **Node order file** (optional) which contains the node order that can be used to speed-up the
  pre-processing when running the command with the same graph later
- **Overlay file** (optional) which contains the description of the hierarchy overlay graph

These 5 input files and 3 output files are described more accurately below.

## Algorithms

The routing script can run three different algorithm types.

- **Dijkstra**: standard time-dependent fastest-path algorithm
- **Time-dependent contraction hierarchies (TCH)**
- **Intersection**

The characteristics and use cases for the algorithm are given below.

- **Dijkstra**: No pre-processing; slow queries. To be used when running a small number of queries.
- **TCH**: Long pre-processing time; fast queries. To be used when running many queries with
  different sources and targets.
- **Intersection**: Longest pre-processing time; fastest queries. To be used when running many
  queries limited to a relatively small set of sources and targets (i.e., *many-to-many*-like
  queries).

You can specify 4 different values for the algorithm to run: *Best*, *Dijkstra*, *TCH* and
*Intersection*.
When specifying *Best*, the algorithm to run is chosen as follows.

- *Dijkstra* if there are less than 100 queries.
- *Intersection* if there are more than 100 queries and less than 2 % of the nodes are used as
  source and less than 2 % of the nodes are used as target.
- *TCH* otherwise.

*TCH reference:*

Batz, G. V., Geisberger, R., Sanders, P., & Vetter, C. (2013). Minimum time-dependent travel times with contraction hierarchies. *Journal of Experimental Algorithmics (JEA), 18,* 1-1.

*Intersection algorithm reference:*

Geisberger, R., & Sanders, P. (2010). Engineering time-dependent many-to-many shortest paths computation. In *10th Workshop on Algorithmic Approaches for Transportation Modelling, Optimization, and Systems (ATMOS'10).* Schloss Dagstuhl-Leibniz-Zentrum fuer Informatik.

## Graph file

The graph file contains a list of directed edges used to build the graph where the queries are run.

There is no constraint for the number of edges that the graph can have.
Also, the graph does not have to be connected (the travel time between two unconnected nodes is
infinite).

The nodes are assumed to be number from `0` to `n-1`, where `n` is the number of nodes (with at
least one incoming or outgoing edge) in the graph.

This JSON file must be an Array of Objects where each Object represents an edge and has the following
fields:

- `source` (integer): index of the source node
- `target` (integer): index of the target node
- `weight` (`TTF`, optional): travel time on the edge (see [Representing travel-time
  functions](../getting_started/ttf.md))

If the weight is not specified, it is assumed to be a constant travel time of 1 second.

An example of triangle graph would be

```json
[
  {
    "source": 0,
    "target": 1,
    "weight": 30.0
  },
  {
    "source": 1,
    "target": 2,
    "weight": {
      "points": [
        [0.0, 10.0],
        [10.0, 20.0],
        [20.0, 15.0]
      ],
      "period": [0.0, 20.0]
    }
  },
  {
    "source": 2,
    "target": 0
  }
]
```

> Note. Usually, the nodes of a graph are identified by some unique ids. These ids are not used
> here, only the nodes' indices are used. It is the users' responsibility to map an unique index
> (between `0` and `n-1`) to each node id of the graph.
>
> For example, one could assume that the node
> with index `0` is the node with the smallest id, the node with index `1` is the node with the
> second-smallest id and so on.
> In this case, for a graph with 3 nodes with ids `101`, `103` and `104`, the node id `101`
> corresponds to index `0`, the node id `103` corresponds to index `1` and the node id `104`
> corresponds to index `2`.

Alternatively, instead of using Objects, you can use Arrays to represent edges, where the first
value is an integer corresponding to the source node, the second value is an integer corresponding
to the target node and the third value (optional) is a `TTF`.
Then, the above example can be written more compactly as

```json
[
  [0, 1, 30.0],
  [
    1,
    2,
    {
      "points": [
        [0.0, 10.0],
        [10.0, 20.0],
        [20.0, 15.0]
      ],
      "period": [0.0, 20.0]
    }
  ],
  [2, 0]
]
```

## Queries file

The queries file contains all the queries that should be executed by the command.

There is no constraint for the number of queries.
Available query types are **point-to-point earliest-arrival queries** and **point-to-point profile
queries** (see [Terminology](routing_script.md#terminology)).

This JSON file must be an Array of Objects where each Object represents a query and has the following
fields:

- `source` (integer): index of the source node
- `target` (integer): index of the target node
- `departure_time` (float, optional): time of departure from the source node, in number of seconds
  since midnight (leave empty for profile queries)

Alternatively, instead of using Objects, you can use Arrays where the first value is an integer
corresponding to the source node, the second value is an integer corresponding to the target node
and the third value (optional) is a float corresponding to the departure time.

For example, if you want to run an earliest-arrival query from node 0 to node 1 with departure time
70.0 (i.e., 00:01:10) and a profile query from node 2 to node 3, you can use the following

```json
[
  {"source": 0, "target": 1, "departure_time": 70.0},
  {"source": 2, "target": 3}
]
```

or

```json
[
  [0, 1, 70.0],
  [0, 2]
]
```

## Weights file

The weights file is an optional file that can be used to specify the weights of the graph's edges.

When using a weights file, you do not have to specify the weights of all the edges in it.
The following priority order is used to set the weight of an edge.

1. Use the weight specified for this edge in the weights file.
2. Use the weight specified for this edge in the graph file (see [Graph
   file](routing_script.md#graph-file)).
3. Use a constant weight of 1 second.

This JSON file must be an Object whose keys are the edge indices and whose values are `TTF` with the
travel-time function of the edges (see [Representing travel-time
functions](../getting_started/ttf.md)).

The following example set a travel time of 30 seconds for edge index 0 and a time-dependent travel
time for edge index 1.

```json
{
  "0": 30.0,
  "1": {
    "points": [
      [0.0, 10.0],
      [10.0, 20.0],
      [20.0, 15.0]
    ],
    "period": [0.0, 20.0]
  }
}
```

## Parameters file

The parameters file contains a set of parameters used by the routing script.

All parameters have default values.
If the parameters file is not set, all parameters are set to their default value.

The parameter `algorithm` (string, optional) is used to choose the algorithm to run.
Possible values are `"Best"` (default), `"Dijkstra"`, `"TCH"` or `"Intersection"` (see
[Algorithms](routing_script.md#algorithms)).

The parameter `output_route` (boolean, optional) is used to control whether the routes should be an
output of the script (for earliest-arrival queries only).
The default is to not output the routes.

There are four parameters to control when and how the travel-time functions are simplified.

- `weight_simplification` (`TTFSimplification`, optional): how to simplify the TTFs of the edges
  before doing anything else.
- `overlay_simplification` (`TTFSimplification`, optional): how to simplify the TTFs of the edges
  (original and shortcuts) once the hierarchy overlay is built (for *TCH* and *intersect* algorithms
  only).
- `search_space_simplification` (`TTFSimplification`, optional): how to simplify the TTFs of the
  search spaces (for *intersect* algorithm only).
- `result_simplification` (`TTFSimplification`, optional): how to simplify the resulting TTFs of the
  profile queries.

See [Travel-time function
simplifications](../getting_started/ttf.md#travel-time-function-simplifications) to understand how
TTFs are simplified and what are the possible values for `TTFSimplification`.

There is another parameter `contraction` which is used to control how the hierarchy overlay is
built.
It is recommended to keep the default values (note that it should not impact the results, only the
speed of the contraction process).

<!-- TODO: Document contraction parameters -->

Below is an example of Parameters file.

```json
{
  "algorithm": "Dijkstra",
  "output_route": true,
  "overlay_simplification": {
    "type": "Interval",
    "value": 5.0
  },
  "search_space_simplification": {
    "type": "Bound",
    "value": 1.0
  },
  "result_simplification": "Raw"
}
```

## Node order file

The node order file is both an input and output file which contains the order in which the graph's
nodes should be contracted to build the contraction hierarchy.

The majority of the computation time of the pre-processing part of the command is due to the
computation of the node ordering through a heuristic.
Hence, this pre-processing part can be sped-up significantly if the node ordering is already known.
The main goal of this file is thus to allow to re-use the same node ordering when running the
command multiple times with the same graph.

> Note. The best node ordering (i.e., the node ordering which gives the fastest query-response time)
> depends on the graph and the edges' weights. If the weight of a single edge changes or if an edge
> is added / removed, then the best node ordering can be different. In practice, the same node
> ordering can be used with good results if the changes are small (i.e., only a few edges were added
> or removed, or the weights slightly changed).

This file is not relevant for the *Dijkstra* algorithm.

This JSON file is simply an Array with as many integers as there are nodes in the graph.
The value at index `i` of the Array represents the order of the node with index `i`.

When given as output, the values are ranging from `1` to `n`, where `n` is the number of nodes in
the graph, but, in the input file, you can use any non-negative value.
Nodes with smaller values are contracted earlier.
If two nodes have the same value, the one with the smallest index is contracted first.

The example Node order file below implies that the nodes are contracted in this order `1 -> 0 -> 2`.

```json
[2, 1, 3]
```

## Output file

The Output file contains the results of the queries given as input and some secondary results.

This JSON file is an Object with two keys, `results` and `details`.

The value for key `results` is an Array with the query results.

- For earliest-arrival queries, when `output_route` is `false`, the value is a float, representing
  the earliest possible arrival time from source to target, given the departure time from source.
- For earliest-arrival queries, when `output_route` is `true`, the value is an Array whose first
  value is a float, representing the earliest possible arrival time from source to target, given the
  departure time from source, and whose second value is an Array of integers representing the edge
  indices of the fastest route.
-  For profile queries, the value is a `TTF`, representing the minimum-travel-time function from
  source to target.

The query result is `"null"` if the source and target are not connected.

The value for key `details` is an Object with the following keys.

- `nb_queries`: Number of queries run.
- `preprocessing_time`: Total time spent on the pre-processing part, in seconds.
- `query_time`: Total time spent on computing queries, in seconds.
- `query_time_per_query`: Average time spent per query (excluding the pre-processing time), in
  seconds.
- `total_time`: Total time spent.
- `total_time_per_query`: Total time spent per query (including the pre-processing time), in
  seconds.

Below is an example of Output file for one earliest-arrival query and two profile queries (where the
first one returns a constant travel-time function), with `output_route` set to `false`.

```json
[
  {
    "results": [
      29430.0,
      325.0,
      {
        "points": [
          [18000.0, 70.0],
          [28800.0, 90.0],
          [36000.0, 70.0],
        ],
        "period": [18000.0, 36000.0]
      }
    ]
  },
  {
    "details": {
      "nb_queries": 3,
      "preprocessing_time": 3.0,
      "query_time": 0.6,
      "query_time_per_query": 0.2,
      "total_time": 3.6,
      "total_time_per_query": 1.2
    }
  }
]
```

Below is the same example when `output_route` is set to `true`.

```json
[
  {
    "results": [
      [
        29430.0,
        [1, 2, 0]
      ],
      325.0,
      {
        "points": [
          [18000.0, 70.0],
          [28800.0, 90.0],
          [36000.0, 70.0],
        ],
        "period": [18000.0, 36000.0]
      }
    ]
  },
  {
    "details": {
      "nb_queries": 3,
      "preprocessing_time": 3.0,
      "query_time": 0.6,
      "query_time_per_query": 0.2,
      "total_time": 3.6,
      "total_time_per_query": 1.2
    }
  }
]
```

## Overlay file

The Overlay file is an output file which contains the description of the hierarchy overlay graph.

This file is mainly useful for debugging purposes.
