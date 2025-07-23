elaborate -top arq_formal
clock clk
reset rst

assert -set_helper <embedded>::arq_formal.read_ptr_valid
assert -set_helper <embedded>::arq_formal.send_ptr_valid
assert -set_helper <embedded>::arq_formal.expected_seq_valid
assert -set_helper <embedded>::arq_formal.last_seq_read_ptr_matches

task -create liveness -copy_assumes -copy_asserts

assume -disable {*}[get_property_list -task <embedded> -include {liveness 1 type {assume}}]
#assume -disable arq_formal.link_error_is_fair
assert -disable {*}[get_property_list -task <embedded> -include {liveness 1 type {assert}}]

assert -disable {*}[get_property_list -task liveness -include {liveness 0 type {assert}}]

prove -task liveness -bg
