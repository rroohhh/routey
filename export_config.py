#!/usr/bin/env python3

from .autowrap import pascal_case_to_snake_case

def config_items(config):
    return {
        name: value for name, value in config.__dict__.items() if not name.startswith("_")
    }

indent = "    "

def package_name(config):
    return pascal_case_to_snake_case(config.__module__.split(".")[-1] + config.__name__)

def export_config_vhdl(config):
    p_name = package_name(config)
    generated = f"package {p_name} is\n"
    for name, item in config_items(config).items():
        assert isinstance(item, int)
        generated += f"{indent}constant {name} : integer := {item};\n"
    generated += f"end package {p_name};\n"
    print(generated)

def export_config_sv(config):
    p_name = package_name(config)
    generated = f"package {p_name};\n"
    for name, item in config_items(config).items():
        assert isinstance(item, int)
        generated += f"{indent}localparam int {name} = {item};\n"
    generated += f"endpackage\n"
    print(generated)

def export_config(flavor, config):
    match flavor:
        case "vhdl":
            export_config_vhdl(config)
        case "sv":
            export_config_sv(config)
        case _:
            assert False

if __name__ == "__main__":
    import sys, importlib

    for name in sys.argv[2:]:
        if "(" in name:
            name, args = name.rsplit("(")
        else:
            args = ""

        args = args.removesuffix(")")
        py_module_name, py_class_name = name.rsplit(".", 1)
        py_module = importlib.import_module(py_module_name)
        py_class = py_module.__dict__[py_class_name]

        export_config(sys.argv[1], py_class)
