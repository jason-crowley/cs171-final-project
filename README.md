# cs171-final-project

For our final project, we chose to model the L-game, an abstract sequential 2-player board game where players take turns moving their L-shaped pieces in a 4x4 grid and then optionally moving one of the two netural pieces occupying a 1x1 cell. The game ends when it is a player's turn and they are unable to move their L-piece to a different position, resulting in a win for the opposing player. Our goal in modeling the L-game was to produce traces of games and prove/discover properties of the game.

### structure of the model, tradeoffs, assumptions, scope, limitations

Our newest model includes a Player sig with Red, Blue extending Player to represent the two players in the game. We have a Game sig which has red, blue, neutral, and turn as fields, representing at a given time the positions of the red player's L-piece, blue player's L-piece, neutral pieces, and whose turn it is. We also have an L sig which has cells as a field, a set representing the coordinates of all possible L-shapes on the board.

Our original model used a lot of quantification and symmetry in generating and validating the L-pieces, which was leading to poor performance. Translation times were upwards of 60 seconds for most tests, and generating traces also took about 30 seconds.

To fix these long translation times, we decided to give concrete instance bounds to specify all 48 possible L-pieces so that Forge did not have to spend as much time translating our deeply nested quantification. The way we approached this was to define an L sig, each associated with a set of 4 cell coordinates arranged in an L-shape. We then enumerated all 48 possible L-pieces in our instance bounds. We could then use the L sigs to represent the current positions of the red and blue L-pieces, and easily look up the cell coordinates for a given L sig. By doing this, we went from quantifying over 4^8 8-tuples of Ints to quantifying over only 48 possible Ls. To make sure the instances bounds were correct, we included a test that ensures that all 8-tuples that satisfy isLShape correspond to exactly one L sig.

### what the model proves, testing, changes in goals

We included various model and property-based tests to verify the soundness of our model and prove properties about the underlying L-game. Some model tests include checking that no player can move twice in a row and our Ls test, which tests potential under/overconstraining of our model by making sure every possible L configuration on the board is included in L.cells. We were also able to show some of the properties we wanted our model to prove about L-game in our tests, a few of them being the possibility of winning in two turns as well as it being impossible for any player to win if no one ever moves the neutral pieces. The rest of our tests are documented in the testing section of lgame.frg.

Our goals remained fairly consistent from our proposal. We met our foundation and target goals and added additional tests to prove other similar properties. We did not verify all of the properties listed in our reach goals due to their significant scope and runtimes. However, we were able to include the sudden death variant of the L-game in our model, which we were not sure we would implement from the outset.

### addition of sudden death variant

When we were finished with most of our target goals, we deided to also add in the sudden death variant into our model using modified transition and trace predicates (suddenDeathTrans and suddenDeathTraces). In the sudden death variant of the L-game, players are allowed to move both neutral pieces instead of just zero or one of them, theoretically allowing for more accelerated gameplay towards win/loss. We added this gameplay variant to enhance the flexibility of our model and deepen our understanding of L-game properties, and we have included several tests and run statements that showcase the sudden death variant.

### instructions for running, understanding instances/visualization

We've included six run statements in our file, with each one corresponding to a different type of game trace (explained in lgame.frg). The default uncommented one just produces a trace with a winner. Our visualization.js script should produce a visualization of multiple 4x4 grids, which from top to bottom represent the board and pieces in each game state. In produced traces that show infinite play, an arrow points from the last produced game state to the state where the loop begins.

Demo link: https://youtu.be/YZ1G33jQWkY
