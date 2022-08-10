# Biogen

This is a kind of sandbox to play around with rule based partitioning a
rectangle based on Perlin noise.

The rules need to be expressed somehow and the simplest things I could think of
was a very simple programming language with arithmetic and conditionals and not
much else.
Definitions were added to support bigger programs and aid maintenance of them.

## Roadmap

These are just a bunch of ideas for possible paths forward, categorized by area.


### Scripts
* Implement the Whittaker biome classification without butchering it entirely.
* Add some nuances to the three major biome classes of the alttp example.
* Add acceptable rivers and lakes to the alttp example.


### Language
* Make Perlin debias configurable from scripts.
* Make the variable seed offset configurable from scripts.
* Add a Perlin water variable


### Algorithms

#### Procedure: local-maximum (alt. local-minimum)

Finding a local maximum (or minimum) of a gradient noise function could be done
by picking a starting point and iterating ascending-neighbour (alt. descending
neighbour) until it returns nothing.


#### Procedure: ascending-neighbour (alt. descending neighbour)

##### Inputs
* A cell (G).
* A noise function.

##### Output
* A cell or nothing. Nothing means that the cell is a local maximum (alt.
  minimum).

##### Procedure
1. Construct an empty set (O).
2. Construct an empty set (C).
3. Construct an empty set (H).
4. Set number (E) to the level of G.
5. Add the given cell to O.
6. While O is non-empty:
   1. Remove a cell (M) from O.
   2. Add M to C.
   3. For each neighbour (N) of M:
      1. If it is preesnt in O or C, skip it.
      2. If N is at the exact same level as G, add it to O.
      3. If the level of N is equal to E, add N to H.
      4. If the level of N is higher than E, clear H and add N to it.
5. If H is empty, return nothing.
6. For each cell (N) in H:
   1. If it is closer to the center of the board than any other cell in H,
      remove it from the set.
7. For each cell (N) in H:
   1. If it is further to the south than any other cell in H, remove it from the
      set.
8. For each cell (N) in H:
   1. If it is further to the west than any other cell in H, remove it from the
      set.
9. Assertion: H contains exactly one cell.
10. Return the single cell of H.

##### Notes
* The procedure described here makes sure to be deterministic.
  This is important.
* The procedure described here may return a cell that is not adjacent to the
  given cell.
  This may be problematic.


#### Perlin water variable

1. Pick a random cell.
2. Calculate its local-maximum.


### Compiler

### Tool
