# Impart

This is a kind of sandbox to play around with rule based partitioning a
rectangle based on Perlin noise.

The rules need to be expressed somehow and the simplest things I could think of
was a very simple programming language with arithmetic and conditionals and not
much else.
Definitions were added to support bigger programs and aid maintenance of them.

The name is short for image partition.
It also alludes to how a structure of domains is imparted to the image.


## Roadmap

These are just a bunch of ideas for possible paths forward, categorized by area.


### Documentation
* Add section about usage.
* Add section about installation.


### Scripts
* Implement the Whittaker biome classification without butchering it entirely.
* Add some nuances to the three major biome classes of the alttp example.
* Add acceptable rivers and lakes to the alttp example.


### Language
* Make Perlin debias configurable from scripts.
* Make the variable seed offset configurable from scripts.
* Add a Perlin water variable.
* Add random constant variable? (Usecases for this?)
* Closures and lists?
  * min() and max()
* Records and modules?
* Sum-types and pattern matching?


### Compiler
* Pretty printer.
  * Make lexer tokens for whitespace and comments.
  * Make AST track whitespace and comments.
  * Nice-looking serializer for AST.
* Make AST the sole tree representation.
  * Support inline comments.
  * Make AST nodes house a generic payload element.
  * Make typechecker and optimization passes return ASTs.
  * Make optimized nodes track their original sub-ASTs.
  * Serialize optimized nodes with their original ASTs commented out.
* Memoize reference evaluation
  * Today we're threading a cell through the runtime evaluation.
    * Refactor it into a more general context.
  * Replace LetIn refcounting with evaluation state in a symbol table in the
    context.
* Stack machine


### Tool
* Make CLI take script file a positional argument instead of a named one.


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
* A cell or nothing. Nothing means that the cell is at a local maximum (alt.
  minimum).

##### Procedure
 1. Construct an empty set (O).
 2. Construct an empty set (C).
 3. Construct an empty set (H).
 4. Add the given cell to O.
 5. While O is non-empty:
    1. Remove a cell (M) from O.
    2. Add M to C.
    3. For each neighbour (N) of M:
       1. If N is a member of either O or C, skip it.
       2. If N is at the exact same level as G, add it to O.
       3. If N is higher than G, add it to H.
 6. If H is empty, return nothing.
 7. If H contains at least one cell that is adjacent to G:
    1. Remove all cells from H that are not adjacent to G.
 8. If H does not contain any cells that are adjacent to G:
    1. For each cell (N) in H:
       1. If it is further from G than any other cell in H,
          remove it from the set.
 9. For each cell (N) in H:
    1. If it is lower than any other cell in H,
       remove it from the set.
10. For each cell (N) in H:
    1. If it is closer to the center of the board than any other cell in H,
       remove it from the set.
11. For each cell (N) in H:
    1. If it is further to the south than any other cell in H, remove it from the
       set.
12. For each cell (N) in H:
    1. If it is further to the west than any other cell in H, remove it from the
       set.
14. Assertion: H contains exactly one cell.
15. Return the single cell of H.

##### Notes
* The procedure described here may return a cell that is not adjacent to the
  given cell.
  There are pathological cases where a strangely shaped plateau could cause this
  algorithm to return a cell with no simple path across the plateau to the given
  value.
* The procedure described here makes sure to be deterministic.
  This is important.
  Its behavior should even be stable across different versions of the software.
