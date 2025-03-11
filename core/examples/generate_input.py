import os
import json

import polars as pl

# Directory where the output files should be stored.
OUTPUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data/")


def get_struct_schema(name, columns):
    """Returns a dictionary mapping simple column names to complete column names for Structs."""
    return {col: f"{name}.{col}" for col in columns}


parameters = {
    "period": [21600, 43200],
    "road_network": {
        "recording_interval": 30 * 60,
        "approximation_bound": 1.0,
        "spillback": True,
        "backward_wave_speed": 4.0,
        "max_pending_duration": 20.0,
        "constrain_inflow": True,
        "algorithm_type": "Best",
        "contraction": {
            "complexity_quotient_weight": 2.0,
            "edge_quotient_weight": 2.0,
            "hierarchy_depth_weight": 1.0,
            "thin_profile_interval_hop_limit": 16,
            "unpacked_edges_quotient_weight": 1.0,
        },
    },
    "learning_model": {"type": "Exponential", "value": 0.01},
    "init_iteration_counter": 1,
    "max_iterations": 2,
    "update_ratio": 1.0,
    "random_seed": 19960813,
    "nb_threads": 24,
    "only_compute_decisions": False,
}

agents = pl.DataFrame(
    {
        "agent_id": [0, 1, 2],
        "alt_choice.type": ["Deterministic", "Deterministic", "Logit"],
        "alt_choice.u": [0.3, 0.6, 0.5],
        "alt_choice.mu": [None, None, 1.0],
        "alt_choice.constants": [None, [0.9, 1.3, 2.1], None],
    }
)

alts = pl.DataFrame(
    {
        "agent_id": [0, 1, 1, 1, 2],
        "alt_id": [0, 0, 1, 2, 0],
        "origin_delay": [None, 30.0, 0.0, None, None],
        "dt_choice.type": ["Constant", "Continuous", "Continuous", "Continuous", "Discrete"],
        "dt_choice.departure_time": [8.0 * 3600, None, None, None, None],
        "dt_choice.period": [None, None, None, None, [7.0 * 3600.0, 8.0 * 3600.0]],
        "dt_choice.interval": [None, None, None, None, 15.0 * 60.0],
        "dt_choice.model.type": [None, "Logit", "Logit", "Logit", "Deterministic"],
        "dt_choice.model.u": [None, 0.1, 0.6, 0.3, 0.9],
        "dt_choice.model.mu": [None, 1.0, 2.0, 0.5, None],
        "dt_choice.model.constants": [None, None, None, None, [1.0, 1.1, 0.7, 2.3]],
        "dt_choice.offset": [None, None, None, None, -4.0 * 60.0],
        "constant_utility": [3.0, -5.0, 0.0, None, None],
        "total_travel_utility.one": [-10.0 / 3600.0, 0.01, 0.0, None, None],
        "total_travel_utility.two": [None, -0.01, None, None, None],
        "total_travel_utility.three": [None, 0.01, 0.0, None, None],
        "total_travel_utility.four": [None, -0.001, 0.0, None, None],
        "origin_utility.type": [None, "Linear", None, None, None],
        "origin_utility.tstar": [None, 7.0 * 3600.0, None, None, None],
        "origin_utility.beta": [None, 5.0 / 3600.0, None, None, None],
        "origin_utility.gamma": [None, 5.0 / 3600.0, None, None, None],
        "origin_utility.delta": [None, 3600.0, None, None, None],
        "destination_utility.type": [None, None, None, "Linear", None],
        "destination_utility.tstar": [None, None, None, 9.0 * 3600.0, None],
        "destination_utility.beta": [None, None, None, 5.0 / 3600.0, None],
        "destination_utility.gamma": [None, None, None, 15.0 / 3600.0, None],
        "destination_utility.delta": [None, None, None, None, None],
        "pre_compute_route": [None, True, False, None, None],
    }
)


trips = pl.DataFrame(
    {
        "agent_id": [1, 1, 1, 2, 2],
        "alt_id": [0, 1, 2, 0, 0],
        "trip_id": [0, 1, 2, 3, 4],
        "class.type": ["Road", "Virtual", "Virtual", "Road", "Road"],
        "class.origin": [1, None, None, 1, 3],
        "class.destination": [4, None, None, 3, 4],
        "class.vehicle": [1, None, None, 2, 3],
        "class.route": [[1, 2, 3], None, None, None, None],
        "class.travel_time": [None, 5.0 * 60.0, 7.0 * 60.0, None, None],
        "stopping_time": [None, None, None, 5.0 * 60.0, None],
        "constant_utility": [0.0, None, 1.0, -1.0, -2.0],
        "travel_utility.one": [0.0, None, -12.0 / 3600.0, -0.02, -0.02],
        "travel_utility.two": [0.0, None, None, 0.01, 0.01],
        "travel_utility.three": [0.0, None, None, -0.005, -0.005],
        "travel_utility.four": [0.0, None, None, 0.01, 0.01],
        "schedule_utility.type": [None, None, None, "Linear", "Linear"],
        "schedule_utility.tstar": [None, None, None, 8.0 * 3600.0, 9.0 * 3600.0],
        "schedule_utility.beta": [None, None, None, 3.0 / 3600.0, None],
        "schedule_utility.gamma": [None, None, None, 3.0 / 3600.0, 20.0 / 3600.0],
        "schedule_utility.delta": [None, None, None, 5.0 * 60.0, 10.0 * 60.00],
    }
)

edges = pl.DataFrame(
    {
        "edge_id": [1, 2, 3],
        "source": [1, 2, 3],
        "target": [2, 3, 4],
        "speed": [50.0 / 3.6, 30.0 / 3.6, 90.0 / 3.6],
        "length": [100.0, 30.0, 60.0],
        "lanes": [2.0, 0.5, None],
        "speed_density.type": [None, "Bottleneck", "ThreeRegimes"],
        "speed_density.capacity": [None, 900.0 * 8.0 / 3600.0, None],
        "speed_density.min_density": [None, None, 0.2],
        "speed_density.jam_density": [None, None, 0.8],
        "speed_density.jam_speed": [None, None, 10.0 / 3.6],
        "speed_density.beta": [None, None, 1.0],
        "bottleneck_flow": [1200.0 / 3600.0, None, 1800.0 / 3600.0],
        "constant_travel_time": [None, 0.0, 3.0],
        "overtaking": [True, False, None],
    }
)

vehicles = pl.DataFrame(
    {
        "vehicle_id": [1, 2, 3, 4],
        "headway": [8.0, 24.0, 0.0, 8.0],
        "pce": [None, 3.0, 0.1, 1.0],
        "speed_function.type": [None, "UpperBound", "Multiplicator", "Piecewise"],
        "speed_function.upper_bound": [None, 90.0 / 3.6, None, None],
        "speed_function.coef": [None, None, 0.8, None],
        "speed_function.x": [None, None, None, [50.0 / 3.6, 90.0 / 3.6, 110.0 / 3.6, 130.0 / 3.6]],
        "speed_function.y": [None, None, None, [50.0 / 3.6, 80.0 / 3.6, 90.0 / 3.6, 90.0 / 3.6]],
        "allowed_edges": [[1, 2, 3], None, None, None],
        "restricted_edges": [None, None, None, [2, 3]],
    }
)

# Create initial road-network conditions for vehicle id 2 and edges 1, 2, 3.
# The road-network conditions are equal to the free-flow travel time for the first half of the
# period and they are equal to double the free-flow travel time for the second half.
ttf_intervals = list(
    range(
        parameters["period"][0],
        parameters["period"][1],
        parameters["road_network"]["recording_interval"],
    )
)
fftt = list(edges["length"] / edges["speed"])
n = len(ttf_intervals)
n0 = n // 2
n1 = n // 2 + n % 2
tts = (
    [fftt[0]] * n0
    + [fftt[0] * 2] * n1
    + [fftt[1]] * n0
    + [fftt[1] * 2] * n1
    + [fftt[2]] * n0
    + [fftt[2] * 2] * n1
)
edge_ttfs = pl.DataFrame(
    {
        "vehicle_id": [2] * n * 3,
        "edge_id": [1] * n + [2] * n + [3] * n,
        "departure_time": ttf_intervals * 3,
        "travel_time": tts,
    }
)

# === Unnested Parquet format ===
directory = os.path.join(OUTPUT_DIR, "unnested_parquet")
if not os.path.isdir(directory):
    os.makedirs(directory)
agents.write_parquet(os.path.join(directory, "agents.parquet"), use_pyarrow=True)
alts.write_parquet(os.path.join(directory, "alts.parquet"), use_pyarrow=True)
trips.write_parquet(os.path.join(directory, "trips.parquet"), use_pyarrow=True)
edges.write_parquet(os.path.join(directory, "edges.parquet"), use_pyarrow=True)
vehicles.write_parquet(os.path.join(directory, "vehicles.parquet"), use_pyarrow=True)
edge_ttfs.write_parquet(os.path.join(directory, "edge_ttfs.parquet"), use_pyarrow=True)
parameters["input_files"] = {
    "agents": "agents.parquet",
    "alternatives": "alts.parquet",
    "trips": "trips.parquet",
    "edges": "edges.parquet",
    "vehicle_types": "vehicles.parquet",
    "road_network_conditions": "edge_ttfs.parquet",
}
parameters["output_directory"] = "output"
parameters["saving_format"] = "Parquet"
with open(os.path.join(directory, "parameters.json"), "w") as f:
    json.dump(parameters, f, indent=2)

# === Nested Parquet format ===
alt_choice_schema = get_struct_schema("alt_choice", ("type", "u", "mu", "constants"))
nested_agents = agents.select(
    "agent_id",
    pl.struct(**alt_choice_schema).alias("alt_choice"),
)

dt_choice_schema = get_struct_schema(
    "dt_choice", ("type", "departure_time", "period", "interval", "offset")
)
dt_choice_model_schema = get_struct_schema("dt_choice.model", ("type", "u", "mu", "constants"))
total_travel_utility_schema = get_struct_schema(
    "total_travel_utility", ("one", "two", "three", "four")
)
origin_utility_schema = get_struct_schema(
    "origin_utility", ("type", "tstar", "beta", "gamma", "delta")
)
destination_utility_schema = get_struct_schema(
    "destination_utility", ("type", "tstar", "beta", "gamma", "delta")
)
nested_alts = alts.select(
    "agent_id",
    "alt_id",
    "origin_delay",
    pl.struct(**dt_choice_schema, model=pl.struct(**dt_choice_model_schema)).alias("dt_choice"),
    "constant_utility",
    pl.struct(**total_travel_utility_schema).alias("total_travel_utility"),
    pl.struct(**origin_utility_schema).alias("origin_utility"),
    pl.struct(**destination_utility_schema).alias("destination_utility"),
    "pre_compute_route",
)

class_schema = get_struct_schema(
    "class", ("type", "origin", "destination", "vehicle", "route", "travel_time")
)
travel_utility_schema = get_struct_schema("travel_utility", ("one", "two", "three", "four"))
schedule_utility_schema = get_struct_schema(
    "schedule_utility", ("type", "tstar", "beta", "gamma", "delta")
)
nested_trips = trips.select(
    "agent_id",
    "alt_id",
    "trip_id",
    pl.struct(**class_schema).alias("class"),
    "stopping_time",
    "constant_utility",
    pl.struct(**travel_utility_schema).alias("travel_utility"),
    pl.struct(**schedule_utility_schema).alias("schedule_utility"),
)

speed_density_schema = get_struct_schema(
    "speed_density", ("type", "capacity", "min_density", "jam_density", "jam_speed", "beta")
)
nested_edges = edges.select(
    "edge_id",
    "source",
    "target",
    "speed",
    "length",
    "lanes",
    pl.struct(**speed_density_schema).alias("speed_density"),
    "bottleneck_flow",
    "constant_travel_time",
    "overtaking",
)

speed_function_schema = get_struct_schema(
    "speed_function", ("type", "upper_bound", "coef", "x", "y")
)
nested_vehicles = vehicles.select(
    "vehicle_id",
    "headway",
    "pce",
    pl.struct(**speed_function_schema).alias("speed_function"),
    "allowed_edges",
    "restricted_edges",
)

directory = os.path.join(OUTPUT_DIR, "parquet")
if not os.path.isdir(directory):
    os.makedirs(directory)
nested_agents.write_parquet(os.path.join(directory, "agents.parquet"), use_pyarrow=True)
nested_alts.write_parquet(os.path.join(directory, "alts.parquet"), use_pyarrow=True)
nested_trips.write_parquet(os.path.join(directory, "trips.parquet"), use_pyarrow=True)
nested_edges.write_parquet(os.path.join(directory, "edges.parquet"), use_pyarrow=True)
nested_vehicles.write_parquet(os.path.join(directory, "vehicles.parquet"), use_pyarrow=True)
edge_ttfs.write_parquet(os.path.join(directory, "edge_ttfs.parquet"), use_pyarrow=True)
parameters["input_files"] = {
    "agents": "agents.parquet",
    "alternatives": "alts.parquet",
    "trips": "trips.parquet",
    "edges": "edges.parquet",
    "vehicle_types": "vehicles.parquet",
    "road_network_conditions": "edge_ttfs.parquet",
}
parameters["output_directory"] = "output"
parameters["saving_format"] = "Parquet"
with open(os.path.join(directory, "parameters.json"), "w") as f:
    json.dump(parameters, f, indent=2)

# === CSV format ===
# Some columns are not supported for CSV format.
agents = agents.drop("alt_choice.constants")
alts = alts.drop("dt_choice.period", "dt_choice.model.constants")
trips = trips.drop("class.route")
vehicles = vehicles.drop(
    "speed_function.x", "speed_function.y", "allowed_edges", "restricted_edges"
)
vehicles = vehicles.with_columns(
    pl.Series([None, "UpperBound", "Multiplicator", None]).alias("speed_function.type")
)
directory = os.path.join(OUTPUT_DIR, "csv")
if not os.path.isdir(directory):
    os.makedirs(directory)
agents.write_csv(os.path.join(directory, "agents.csv"))
alts.write_csv(os.path.join(directory, "alts.csv"))
trips.write_csv(os.path.join(directory, "trips.csv"))
edges.write_csv(os.path.join(directory, "edges.csv"))
vehicles.write_csv(os.path.join(directory, "vehicles.csv"))
edge_ttfs.write_csv(os.path.join(directory, "edge_ttfs.csv"))
parameters["input_files"] = {
    "agents": "agents.csv",
    "alternatives": "alts.csv",
    "trips": "trips.csv",
    "edges": "edges.csv",
    "vehicle_types": "vehicles.csv",
    "road_network_conditions": "edge_ttfs.csv",
}
parameters["output_directory"] = "output"
parameters["saving_format"] = "CSV"
with open(os.path.join(directory, "parameters.json"), "w") as f:
    json.dump(parameters, f, indent=2)
