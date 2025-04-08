#!/usr/bin/env sh

# echo $0

export SBY=yowasp-sby
uv run python -m export_config sv memory_mapped_router.Config > gen/router_pkg.sv
uv run python -m export_config vhdl memory_mapped_router.Config > gen/router_pkg.vhd
uv run python -m memory_mapped_router generate > gen/router_impl.sv
uv run python -m autowrap 'memory_mapped_router.MemoryMappedRouter()' > gen/router.sv
