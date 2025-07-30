#!/usr/bin/env sh

# echo $0

export SBY=yowasp-sby
uv run python -m export_config sv memory_mapped_router.Config > gen/router_pkg.sv
uv run python -m export_config vhdl memory_mapped_router.Config > gen/router_pkg.vhd
uv run python -m autowrap --platform tsmc -i 'fatmeshy_router_top.RouterTop()' > gen/router.sv
