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


### Algorithms

#### Procedure: ascending-neighbour (alt. descending-neighbour)

Finding a local maximum (or minimum) of a gradient noise function could be done
by picking a starting point and finding the highest (lowest) one of its
neighbours, and iterate until none of the neighbours are higer (or lower) than
the current cell.

In theory multiple cells could be the highest ones for a given step.
A reasonable set of simple tie breakers would be:
1. Pick the cell that is furthest from the center of the board (or closest to it
   when descending).
2. Pick the cell that is furthest to the north (or south when descending).
3. Pick the cell that is furthest to the eastt (or west when descending).


### Compiler

### Tool
