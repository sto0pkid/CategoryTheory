module LogicGates where

open import Agda.Primitive

data Bit : Set where
 on : Bit
 off : Bit

wire : Bit → Bit
wire on = on
wire off = off

not-gate : Bit → Bit
not-gate on = off
not-gate off = on

and-gate : Bit → Bit → Bit
and-gate on on = on
and-gate on off = off
and-gate off on = off
and-gate off off = off

or-gate : Bit → Bit → Bit
or-gate on on = on
or-gate on off = on
or-gate off on = on
or-gate off off = off

nand-gate : Bit → Bit → Bit
nand-gate on on = off
nand-gate on off = on
nand-gate off on = on
nand-gate off off = on

nor-gate : Bit → Bit → Bit
nor-gate on on = off
nor-gate on off = off
nor-gate off on = off
nor-gate off off = on

xor-gate : Bit → Bit → Bit
xor-gate on on = off
xor-gate on off = on
xor-gate off on = on
xor-gate off off = off

