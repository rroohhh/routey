elaborate -top arq_formal
clock clk
reset rst

task -create liveness -copy_assumes -copy_asserts

assume -disable {*}[get_property_list -task <embedded> -include {liveness 1 type {assume}}]
#assume -disable arq_formal.link_error_is_fair
assert -disable {*}[get_property_list -task <embedded> -include {liveness 1 type {assert}}]

assert -disable {*}[get_property_list -task liveness -include {liveness 0 type {assert}}]

prove -task liveness -bg
