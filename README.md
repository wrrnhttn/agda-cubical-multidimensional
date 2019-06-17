# Multidimensional data in Cubical Agda

This is an experimental library for multidimensionial data types
(Morton numbers, n-dimensional trees, etc.) in Cubical Agda. See
[Morton](https://github.com/JaneliaSciComp/Morton.jl) and
[RegionTrees](https://github.com/rdeits/RegionTrees.jl)
for comparable libraries in Julia.

The goal is to explore potential uses of transport in obtaining efficiencies in
computations on multidimensonal spatial data; see the
[BinNat](https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda)
module of the Cubical Agda library for an example of this approach.

DISCLAIMER: The library is intended by the author to be a project for learning
Agda  and cubical type theory, so expect the code to be naive, inefficient,
and possibly incorrect, in an unconventional style. Suggestions for improvement
would be warmly welcomed.