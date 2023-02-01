import os

from json_schema_for_humans.generate import generate_from_filename
from json_schema_for_humans.generation_configuration import GenerationConfiguration

MD_CONFIG = GenerationConfiguration(
    expand_buttons=True,
    template_name="md",
    link_to_reused_ref=False,
    markdown_options={
        "fenced-code-blocks": {"cssclass": "highlight jumbotron"},
        "tables": None,
        "break-on-newline": True,
        "cuddled-lists": True,
    },
    template_md_options={"badge_as_image": True, "show_heading_numbers": False},
    with_footer=False,
)

JS_CONFIG = GenerationConfiguration(
    expand_buttons=True,
    template_name="js",
    link_to_reused_ref=False,
    markdown_options={
        "fenced-code-blocks": {"cssclass": "highlight jumbotron"},
        "tables": None,
        "break-on-newline": True,
        "cuddled-lists": True,
    },
    template_md_options={"badge_as_image": True, "show_heading_numbers": False},
    with_footer=False,
)

PATH = "schemas/metropolis/"
SCHEMAS = [
    "agents",
    "roadnetwork",
    "parameters",
    "aggregate-results",
    "agent-results",
    "skim-results",
    "weight-results",
]
if os.path.isdir(PATH):
    for SCHEMA in SCHEMAS:
        SCHEMA_FILE = PATH + SCHEMA
        generate_from_filename(SCHEMA_FILE + ".json", SCHEMA_FILE + ".md", config=MD_CONFIG)
        generate_from_filename(SCHEMA_FILE + ".json", SCHEMA_FILE + ".html", config=JS_CONFIG)

PATH = "schemas/tch/"
SCHEMAS = ["queries", "graph", "weights", "parameters", "node-order", "output"]
if os.path.isdir(PATH):
    for SCHEMA in SCHEMAS:
        SCHEMA_FILE = PATH + SCHEMA
        generate_from_filename(SCHEMA_FILE + ".json", SCHEMA_FILE + ".md", config=MD_CONFIG)
        generate_from_filename(SCHEMA_FILE + ".json", SCHEMA_FILE + ".html", config=JS_CONFIG)
