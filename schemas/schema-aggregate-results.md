# AggregateResults_for_double

- [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus`](#surplus)
  - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > mean`](#surplus_mean)
  - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > std`](#surplus_std)
  - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > min`](#surplus_min)
  - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > max`](#surplus_max)
- [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results`](#mode_results)
  - [![Optional](https://img.shields.io/badge/Optional-yellow) Property `AggregateResults_for_double > mode_results > road`](#mode_results_road)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > count`](#mode_results_road_count)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion`](#mode_results_road_congestion)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > mean`](#mode_results_road_congestion_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > std`](#mode_results_road_congestion_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > min`](#mode_results_road_congestion_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > max`](#mode_results_road_congestion_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times`](#mode_results_road_departure_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > mean`](#mode_results_road_departure_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > std`](#mode_results_road_departure_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > min`](#mode_results_road_departure_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > max`](#mode_results_road_departure_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times`](#mode_results_road_arrival_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > mean`](#mode_results_road_arrival_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > std`](#mode_results_road_arrival_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > min`](#mode_results_road_arrival_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > max`](#mode_results_road_arrival_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times`](#mode_results_road_road_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > mean`](#mode_results_road_road_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > std`](#mode_results_road_road_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > min`](#mode_results_road_road_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > max`](#mode_results_road_road_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times`](#mode_results_road_in_bottleneck_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > mean`](#mode_results_road_in_bottleneck_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > std`](#mode_results_road_in_bottleneck_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > min`](#mode_results_road_in_bottleneck_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > max`](#mode_results_road_in_bottleneck_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times`](#mode_results_road_out_bottleneck_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > mean`](#mode_results_road_out_bottleneck_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > std`](#mode_results_road_out_bottleneck_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > min`](#mode_results_road_out_bottleneck_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > max`](#mode_results_road_out_bottleneck_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times`](#mode_results_road_travel_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > mean`](#mode_results_road_travel_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > std`](#mode_results_road_travel_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > min`](#mode_results_road_travel_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > max`](#mode_results_road_travel_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times`](#mode_results_road_route_free_flow_travel_times)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > mean`](#mode_results_road_route_free_flow_travel_times_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > std`](#mode_results_road_route_free_flow_travel_times_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > min`](#mode_results_road_route_free_flow_travel_times_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > max`](#mode_results_road_route_free_flow_travel_times_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths`](#mode_results_road_lengths)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > mean`](#mode_results_road_lengths_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > std`](#mode_results_road_lengths_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > min`](#mode_results_road_lengths_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > max`](#mode_results_road_lengths_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts`](#mode_results_road_edge_counts)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > mean`](#mode_results_road_edge_counts_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > std`](#mode_results_road_edge_counts_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > min`](#mode_results_road_edge_counts_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > max`](#mode_results_road_edge_counts_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities`](#mode_results_road_utilities)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > mean`](#mode_results_road_utilities_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > std`](#mode_results_road_utilities_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > min`](#mode_results_road_utilities_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > max`](#mode_results_road_utilities_max)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff`](#mode_results_road_exp_travel_time_diff)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > mean`](#mode_results_road_exp_travel_time_diff_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > std`](#mode_results_road_exp_travel_time_diff_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > min`](#mode_results_road_exp_travel_time_diff_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > max`](#mode_results_road_exp_travel_time_diff_max)
    - [![Optional](https://img.shields.io/badge/Optional-yellow) Property `AggregateResults_for_double > mode_results > road > dep_time_shift`](#mode_results_road_dep_time_shift)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > mean`](#mode_results_road_dep_time_shift_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > std`](#mode_results_road_dep_time_shift_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > min`](#mode_results_road_dep_time_shift_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > max`](#mode_results_road_dep_time_shift_max)
  - [![Optional](https://img.shields.io/badge/Optional-yellow) Property `AggregateResults_for_double > mode_results > constant`](#mode_results_constant)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > count`](#mode_results_constant_count)
    - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility`](#mode_results_constant_utility)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > mean`](#mode_results_constant_utility_mean)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > std`](#mode_results_constant_utility_std)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > min`](#mode_results_constant_utility_min)
      - [![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > max`](#mode_results_constant_utility_max)

**Title:** AggregateResults_for_double

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |

**Description:** Aggregate results summarizing the results of an iteration.

| Property                         | Pattern | Type   | Deprecated | Definition | Title/Description                          |
| -------------------------------- | ------- | ------ | ---------- | ---------- | ------------------------------------------ |
| + [surplus](#surplus )           | No      | object | No         | In         | Distribution of the surplus of the agents. |
| + [mode_results](#mode_results ) | No      | object | No         | In         | Mode-specific aggregate results.           |

## <a name="surplus"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of the surplus of the agents.

| Property                 | Pattern | Type   | Deprecated | Definition                          | Title/Description                                 |
| ------------------------ | ------- | ------ | ---------- | ----------------------------------- | ------------------------------------------------- |
| + [mean](#surplus_mean ) | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [std](#surplus_std )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [min](#surplus_min )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [max](#surplus_max )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |

### <a name="surplus_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > mean`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

### <a name="surplus_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > std`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

### <a name="surplus_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > min`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

### <a name="surplus_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > surplus > max`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

## <a name="mode_results"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Mode-specific aggregate results.

| Property                              | Pattern | Type   | Deprecated | Definition | Title/Description                   |
| ------------------------------------- | ------- | ------ | ---------- | ---------- | ----------------------------------- |
| - [road](#mode_results_road )         | No      | object | No         | In         | Results specific to road modes.     |
| - [constant](#mode_results_constant ) | No      | object | No         | In         | Results specific to constant modes. |

### <a name="mode_results_road"></a>![Optional](https://img.shields.io/badge/Optional-yellow) Property `AggregateResults_for_double > mode_results > road`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Results specific to road modes.

| Property                                                                           | Pattern | Type    | Deprecated | Definition | Title/Description                                                                                                                                                            |
| ---------------------------------------------------------------------------------- | ------- | ------- | ---------- | ---------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| + [count](#mode_results_road_count )                                               | No      | integer | No         | -          | Number of trips taken with a road mode of transportation.                                                                                                                    |
| + [congestion](#mode_results_road_congestion )                                     | No      | object  | No         | In         | The relative difference between average actual travel time and average free-flow travel time.                                                                                |
| + [departure_times](#mode_results_road_departure_times )                           | No      | object  | No         | In         | Distribution of departure times.                                                                                                                                             |
| + [arrival_times](#mode_results_road_arrival_times )                               | No      | object  | No         | In         | Distribution of arrival times.                                                                                                                                               |
| + [road_times](#mode_results_road_road_times )                                     | No      | object  | No         | In         | Distribution of road times.                                                                                                                                                  |
| + [in_bottleneck_times](#mode_results_road_in_bottleneck_times )                   | No      | object  | No         | In         | Distribution of in-bottleneck times.                                                                                                                                         |
| + [out_bottleneck_times](#mode_results_road_out_bottleneck_times )                 | No      | object  | No         | In         | Distribution of out-bottleneck times.                                                                                                                                        |
| + [travel_times](#mode_results_road_travel_times )                                 | No      | object  | No         | In         | Distribution of total travel times.                                                                                                                                          |
| + [route_free_flow_travel_times](#mode_results_road_route_free_flow_travel_times ) | No      | object  | No         | In         | Distribution of route free-flow travel times times.                                                                                                                          |
| + [lengths](#mode_results_road_lengths )                                           | No      | object  | No         | In         | Distribution of route length.                                                                                                                                                |
| + [edge_counts](#mode_results_road_edge_counts )                                   | No      | object  | No         | In         | Distribution of number of edges taken.                                                                                                                                       |
| + [utilities](#mode_results_road_utilities )                                       | No      | object  | No         | In         | Distribution of total utility.                                                                                                                                               |
| + [exp_travel_time_diff](#mode_results_road_exp_travel_time_diff )                 | No      | object  | No         | In         | Distribution of relative difference between expected travel time and actual travel time.                                                                                     |
| - [dep_time_shift](#mode_results_road_dep_time_shift )                             | No      | object  | No         | In         | Distribution of departure time shift compared to previous iteration (except for the first iteration; excluding agents who chose a different mode in the previous iteration). |

#### <a name="mode_results_road_count"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > count`

|            |           |
| ---------- | --------- |
| **Type**   | `integer` |
| **Format** | `uint`    |

**Description:** Number of trips taken with a road mode of transportation.

| Restrictions |          |
| ------------ | -------- |
| **Minimum**  | &ge; 0.0 |

#### <a name="mode_results_road_congestion"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** The relative difference between average actual travel time and average free-flow travel time.

| Property                                      | Pattern | Type   | Deprecated | Definition | Title/Description |
| --------------------------------------------- | ------- | ------ | ---------- | ---------- | ----------------- |
| + [mean](#mode_results_road_congestion_mean ) | No      | number | No         | -          | -                 |
| + [std](#mode_results_road_congestion_std )   | No      | number | No         | -          | -                 |
| + [min](#mode_results_road_congestion_min )   | No      | number | No         | -          | -                 |
| + [max](#mode_results_road_congestion_max )   | No      | number | No         | -          | -                 |

##### <a name="mode_results_road_congestion_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > mean`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_congestion_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > std`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_congestion_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > min`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_congestion_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > congestion > max`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

#### <a name="mode_results_road_departure_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of departure times.

| Property                                           | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| -------------------------------------------------- | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_departure_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_departure_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_departure_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_departure_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_departure_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_departure_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_departure_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_departure_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > departure_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_arrival_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of arrival times.

| Property                                         | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| ------------------------------------------------ | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_arrival_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_arrival_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_arrival_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_arrival_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_arrival_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_arrival_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_arrival_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_arrival_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > arrival_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_road_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of road times.

| Property                                      | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| --------------------------------------------- | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_road_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_road_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_road_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_road_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_road_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_road_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_road_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_road_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > road_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_in_bottleneck_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of in-bottleneck times.

| Property                                               | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| ------------------------------------------------------ | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_in_bottleneck_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_in_bottleneck_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_in_bottleneck_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_in_bottleneck_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_in_bottleneck_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_in_bottleneck_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_in_bottleneck_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_in_bottleneck_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > in_bottleneck_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_out_bottleneck_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of out-bottleneck times.

| Property                                                | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| ------------------------------------------------------- | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_out_bottleneck_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_out_bottleneck_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_out_bottleneck_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_out_bottleneck_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_out_bottleneck_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_out_bottleneck_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_out_bottleneck_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_out_bottleneck_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > out_bottleneck_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_travel_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of total travel times.

| Property                                        | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| ----------------------------------------------- | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_travel_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_travel_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_travel_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_travel_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_travel_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_travel_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_travel_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_travel_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > travel_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_route_free_flow_travel_times"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of route free-flow travel times times.

| Property                                                        | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| --------------------------------------------------------------- | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_route_free_flow_travel_times_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_route_free_flow_travel_times_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_route_free_flow_travel_times_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_route_free_flow_travel_times_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_route_free_flow_travel_times_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_route_free_flow_travel_times_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_route_free_flow_travel_times_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_route_free_flow_travel_times_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > route_free_flow_travel_times > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

#### <a name="mode_results_road_lengths"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of route length.

| Property                                   | Pattern | Type   | Deprecated | Definition                         | Title/Description                                |
| ------------------------------------------ | ------- | ------ | ---------- | ---------------------------------- | ------------------------------------------------ |
| + [mean](#mode_results_road_lengths_mean ) | No      | number | No         | In #/definitions/Length_for_double | Representation of a length, expressed in meters. |
| + [std](#mode_results_road_lengths_std )   | No      | number | No         | In #/definitions/Length_for_double | Representation of a length, expressed in meters. |
| + [min](#mode_results_road_lengths_min )   | No      | number | No         | In #/definitions/Length_for_double | Representation of a length, expressed in meters. |
| + [max](#mode_results_road_lengths_max )   | No      | number | No         | In #/definitions/Length_for_double | Representation of a length, expressed in meters. |

##### <a name="mode_results_road_lengths_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > mean`

|                |                                 |
| -------------- | ------------------------------- |
| **Type**       | `number`                        |
| **Defined in** | #/definitions/Length_for_double |

**Description:** Representation of a length, expressed in meters.

##### <a name="mode_results_road_lengths_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > std`

|                |                                 |
| -------------- | ------------------------------- |
| **Type**       | `number`                        |
| **Defined in** | #/definitions/Length_for_double |

**Description:** Representation of a length, expressed in meters.

##### <a name="mode_results_road_lengths_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > min`

|                |                                 |
| -------------- | ------------------------------- |
| **Type**       | `number`                        |
| **Defined in** | #/definitions/Length_for_double |

**Description:** Representation of a length, expressed in meters.

##### <a name="mode_results_road_lengths_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > lengths > max`

|                |                                 |
| -------------- | ------------------------------- |
| **Type**       | `number`                        |
| **Defined in** | #/definitions/Length_for_double |

**Description:** Representation of a length, expressed in meters.

#### <a name="mode_results_road_edge_counts"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of number of edges taken.

| Property                                       | Pattern | Type   | Deprecated | Definition | Title/Description |
| ---------------------------------------------- | ------- | ------ | ---------- | ---------- | ----------------- |
| + [mean](#mode_results_road_edge_counts_mean ) | No      | number | No         | -          | -                 |
| + [std](#mode_results_road_edge_counts_std )   | No      | number | No         | -          | -                 |
| + [min](#mode_results_road_edge_counts_min )   | No      | number | No         | -          | -                 |
| + [max](#mode_results_road_edge_counts_max )   | No      | number | No         | -          | -                 |

##### <a name="mode_results_road_edge_counts_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > mean`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_edge_counts_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > std`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_edge_counts_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > min`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_edge_counts_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > edge_counts > max`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

#### <a name="mode_results_road_utilities"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of total utility.

| Property                                     | Pattern | Type   | Deprecated | Definition                          | Title/Description                                 |
| -------------------------------------------- | ------- | ------ | ---------- | ----------------------------------- | ------------------------------------------------- |
| + [mean](#mode_results_road_utilities_mean ) | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [std](#mode_results_road_utilities_std )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [min](#mode_results_road_utilities_min )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [max](#mode_results_road_utilities_max )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |

##### <a name="mode_results_road_utilities_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > mean`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

##### <a name="mode_results_road_utilities_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > std`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

##### <a name="mode_results_road_utilities_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > min`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

##### <a name="mode_results_road_utilities_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > utilities > max`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

#### <a name="mode_results_road_exp_travel_time_diff"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of relative difference between expected travel time and actual travel time.

| Property                                                | Pattern | Type   | Deprecated | Definition | Title/Description |
| ------------------------------------------------------- | ------- | ------ | ---------- | ---------- | ----------------- |
| + [mean](#mode_results_road_exp_travel_time_diff_mean ) | No      | number | No         | -          | -                 |
| + [std](#mode_results_road_exp_travel_time_diff_std )   | No      | number | No         | -          | -                 |
| + [min](#mode_results_road_exp_travel_time_diff_min )   | No      | number | No         | -          | -                 |
| + [max](#mode_results_road_exp_travel_time_diff_max )   | No      | number | No         | -          | -                 |

##### <a name="mode_results_road_exp_travel_time_diff_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > mean`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_exp_travel_time_diff_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > std`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_exp_travel_time_diff_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > min`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

##### <a name="mode_results_road_exp_travel_time_diff_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > exp_travel_time_diff > max`

|            |          |
| ---------- | -------- |
| **Type**   | `number` |
| **Format** | `double` |

#### <a name="mode_results_road_dep_time_shift"></a>![Optional](https://img.shields.io/badge/Optional-yellow) Property `AggregateResults_for_double > mode_results > road > dep_time_shift`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of departure time shift compared to previous iteration (except for the first iteration; excluding agents who chose a different mode in the previous iteration).

| Property                                          | Pattern | Type   | Deprecated | Definition                       | Title/Description                                                   |
| ------------------------------------------------- | ------- | ------ | ---------- | -------------------------------- | ------------------------------------------------------------------- |
| + [mean](#mode_results_road_dep_time_shift_mean ) | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [std](#mode_results_road_dep_time_shift_std )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [min](#mode_results_road_dep_time_shift_min )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |
| + [max](#mode_results_road_dep_time_shift_max )   | No      | number | No         | In #/definitions/Time_for_double | Representation of time duration or timestamp, expressed in seconds. |

##### <a name="mode_results_road_dep_time_shift_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > mean`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_dep_time_shift_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > std`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_dep_time_shift_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > min`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

##### <a name="mode_results_road_dep_time_shift_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > road > dep_time_shift > max`

|                |                               |
| -------------- | ----------------------------- |
| **Type**       | `number`                      |
| **Defined in** | #/definitions/Time_for_double |

**Description:** Representation of time duration or timestamp, expressed in seconds.

### <a name="mode_results_constant"></a>![Optional](https://img.shields.io/badge/Optional-yellow) Property `AggregateResults_for_double > mode_results > constant`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Results specific to constant modes.

| Property                                     | Pattern | Type    | Deprecated | Definition | Title/Description                                                    |
| -------------------------------------------- | ------- | ------- | ---------- | ---------- | -------------------------------------------------------------------- |
| + [count](#mode_results_constant_count )     | No      | integer | No         | -          | Number of agents who chose a constant mode.                          |
| + [utility](#mode_results_constant_utility ) | No      | object  | No         | In         | Distribution of the utility of the agents who chose a constant mode. |

#### <a name="mode_results_constant_count"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > count`

|            |           |
| ---------- | --------- |
| **Type**   | `integer` |
| **Format** | `uint`    |

**Description:** Number of agents who chose a constant mode.

| Restrictions |          |
| ------------ | -------- |
| **Minimum**  | &ge; 0.0 |

#### <a name="mode_results_constant_utility"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility`

|                           |                                                                                                                                   |
| ------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| **Type**                  | `object`                                                                                                                          |
| **Additional properties** | [![Any type: allowed](https://img.shields.io/badge/Any%20type-allowed-green)](# "Additional Properties of any type are allowed.") |
| **Defined in**            |                                                                                                                                   |

**Description:** Distribution of the utility of the agents who chose a constant mode.

| Property                                       | Pattern | Type   | Deprecated | Definition                          | Title/Description                                 |
| ---------------------------------------------- | ------- | ------ | ---------- | ----------------------------------- | ------------------------------------------------- |
| + [mean](#mode_results_constant_utility_mean ) | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [std](#mode_results_constant_utility_std )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [min](#mode_results_constant_utility_min )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |
| + [max](#mode_results_constant_utility_max )   | No      | number | No         | In #/definitions/Utility_for_double | Representation of a utility (or monetary) amount. |

##### <a name="mode_results_constant_utility_mean"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > mean`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

##### <a name="mode_results_constant_utility_std"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > std`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

##### <a name="mode_results_constant_utility_min"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > min`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

##### <a name="mode_results_constant_utility_max"></a>![Required](https://img.shields.io/badge/Required-blue) Property `AggregateResults_for_double > mode_results > constant > utility > max`

|                |                                  |
| -------------- | -------------------------------- |
| **Type**       | `number`                         |
| **Defined in** | #/definitions/Utility_for_double |

**Description:** Representation of a utility (or monetary) amount.

----------------------------------------------------------------------------------------------------------------------------
