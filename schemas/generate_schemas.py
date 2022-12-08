from json_schema_for_humans.generate import generate_from_filename
from json_schema_for_humans.generation_configuration import GenerationConfiguration

config = GenerationConfiguration(
    expand_buttons = True,
    template_name = "md",
    link_to_reused_ref = False,
    markdown_options = {
        "fenced-code-blocks": {
            "cssclass": "highlight jumbotron"
        },
        "tables": None,
        "break-on-newline": True,
        "cuddled-lists": True
    },
    template_md_options = {
        "badge_as_image": True,
        "show_heading_numbers": False
    },
    with_footer = False,
)

generate_from_filename("schema-agents.json", "schema-agents.md", config=config)
generate_from_filename("schema-roadnetwork.json", "schema-roadnetwork.md", config=config)
generate_from_filename("schema-parameters.json", "schema-parameters.md", config=config)
generate_from_filename("schema-iteration.json", "schema-iteration.md", config=config)
generate_from_filename("schema-output.json", "schema-output.md", config=config)

config = GenerationConfiguration(
    expand_buttons = True,
    template_name = "js",
    link_to_reused_ref = False,
    markdown_options = {
        "fenced-code-blocks": {
            "cssclass": "highlight jumbotron"
        },
        "tables": None,
        "break-on-newline": True,
        "cuddled-lists": True
    },
    template_md_options = {
        "badge_as_image": True,
        "show_heading_numbers": False
    },
    with_footer = False,
)

generate_from_filename("schema-agents.json", "schema-agents.html", config=config)
generate_from_filename("schema-roadnetwork.json", "schema-roadnetwork.html", config=config)
generate_from_filename("schema-parameters.json", "schema-parameters.html", config=config)
generate_from_filename("schema-iteration.json", "schema-iteration.html", config=config)
generate_from_filename("schema-output.json", "schema-output.html", config=config)
