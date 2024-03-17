import os
import json

import polars as pl

# Directory where the output files should be stored.
OUTPUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data/")


def get_struct_schema(name, columns):
    """Returns a dictionary mapping simple column names to complete column names for Structs."""
    return {col: f"{name}.{col}" for col in columns}


parameters = {
    "algorithm": "TCH",
    "output_route": True,
    "output_order": False,
    "nb_threads": 24,
    "contraction": {
        "complexity_quotient_weight": 2.0,
        "edge_quotient_weight": 2.0,
        "hierarchy_depth_weight": 1.0,
        "thin_profile_interval_hop_limit": 16,
        "unpacked_edges_quotient_weight": 1.0,
    },
}

edges = pl.DataFrame(
    {
        "edge_id": [1, 2, 3],
        "source": [1, 2, 1],
        "target": [2, 3, 3],
        "travel_time": [1.0, 2.0, 2.0],
    }
)

queries = pl.DataFrame(
    {
        "query_id": [1, 2, 3, 4, 5],
        "origin": [1, 1, 1, 3, 3],
        "destination": [3, 3, 3, 1, 1],
        "departure_time": [0.0, 10.0, None, 0.0, None],
    }
)

edge_ttfs = pl.DataFrame(
    {
        "edge_id": [3, 3, 3],
        "departure_time": [0.0, 10.0, 20.0],
        "travel_time": [2.0, 4.0, 2.0],
    }
)

# === Parquet format ===
directory = os.path.join(OUTPUT_DIR, "parquet")
if not os.path.isdir(directory):
    os.makedirs(directory)
edges.write_parquet(os.path.join(directory, "edges.parquet"))
queries.write_parquet(os.path.join(directory, "queries.parquet"))
edge_ttfs.write_parquet(os.path.join(directory, "edge_ttfs.parquet"))
parameters["input_files"] = {
    "queries": "queries.parquet",
    "edges": "edges.parquet",
    "edge_ttfs": "edge_ttfs.parquet",
}
parameters["output_directory"] = "output"
parameters["saving_format"] = "Parquet"
with open(os.path.join(directory, "parameters.json"), "w") as f:
    json.dump(parameters, f, indent=2)

# === CSV format ===
directory = os.path.join(OUTPUT_DIR, "csv")
if not os.path.isdir(directory):
    os.makedirs(directory)
edges.write_csv(os.path.join(directory, "edges.csv"))
queries.write_csv(os.path.join(directory, "queries.csv"))
edge_ttfs.write_csv(os.path.join(directory, "edge_ttfs.csv"))
parameters["input_files"] = {
    "queries": "queries.csv",
    "edges": "edges.csv",
    "edge_ttfs": "edge_ttfs.csv",
}
parameters["output_directory"] = "output"
parameters["saving_format"] = "CSV"
with open(os.path.join(directory, "parameters.json"), "w") as f:
    json.dump(parameters, f, indent=2)
