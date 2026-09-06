#!/usr/bin/env python3

# Exact integer control showing why the Round-22 chain `y <= x <= z`
# did not cover the actual inherited remaining branch `y <= z < x`.
y, z, x = 5, 7, 11
assert y <= z < x
assert not (x <= z)
assert y <= x and y <= z

# Mutation: if one accidentally reintroduces `x <= z` as a premise,
# this genuine remaining-order control would be excluded.
old_chain_applies = (y <= x <= z)
new_min_scope_applies = (y <= x and y <= z)
remaining_scope_applies = (y <= z < x)
assert not old_chain_applies
assert new_min_scope_applies
assert remaining_scope_applies

print("PASS order-scope semantic control")
print("control=(y,z,x)=(5,7,11)")
print("old_chain_applies=false")
print("new_min_scope_applies=true")
print("remaining_scope_applies=true")
