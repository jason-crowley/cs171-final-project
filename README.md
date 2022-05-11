# cs171-final-project

You should write a one page README describing how you structured your model and what your model proved. You can assume that anyone reading it will be familiar with your project proposal. Here are some examples of points you might cover:

    What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

    What assumptions did you make about scope? What are the limits of your model?

    Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

    How should we understand an instance of your model and what your custom visualization shows?




    We chose to model the L game, an abstract sequential 2-player board game where players take turns moving their L-shaped pieces in a 4x4 grid
    and then have the option of moving one of the two netural pieces occupying a 1x1 cell. The game ends when it is a player's turn and they are unable
    to move their L to a different position, resulting in them losing the game....

    -- structure of the model, tradeoffs, assumptions, scope, limitations
    Our newest model includes a Player sig with Red, Blue extending Player to represent the two players in the game. We have a Game sig which has red, blue, neutral, and turns as fields, representing at a given time the positions of the red player's piece, blue player's piece, neutral pieces, and whose turn it is.
    We also have an L sig which has cells as a field, a set representing the coordinates of all possible L-shapes on the board.

    Our original model used a lot of quantification and symmetry in generating and validating the L-pieces, which was leading to poor performance. Translation times were upwards of 60 seconds for most tests, and generating traces also took about 30 seconds.

            -- stuff about the changes Jason made with inst

    -- what the model proves, testing, change in goals

    We were able to show some of the properties we wanted our model to prove about L-game in our tests, a few of them being the possibility of winning in two turns as well as it being impossible to win without having moved a neutral piece.
    One example of how we tested potential under/overconstraining of our model is in our Ls test, where we make sure every possible L configuration on the board is included in L.cells.
    The rest of our tests are documented in the testing section of lgame.frg.


    -- addition of sudden death variant
    When we were finished with most of our target goals, we deided to also add in the sudden death variant into our model. In the sudden death variant, players are allowed to move both neutral pieces instead of just zero or one of them, theoretically allowing for more accelerated gameplay towards win/loss.

    -- instructions for running, understanding instances/visualization
    We've included six run statements in our file, with each one corresponding to a different type of game trace (explained in lgame.frg). The default uncommented one just produces a trace with a winner. Our visualization.js script should produce a visualization of multiple 4x4 grids, which from top to bottom represent the board and pieces in each game state. In produced traces that show infinite play, an arrow points from the last produced game state to the state where the loop begins.
