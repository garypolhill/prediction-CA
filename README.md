# PredictionCA.nlogo
A NetLogo model enabling exploration of the predictability of elementary cellular automata

This is the NetLogo (6.1.0) code accompanying a presentation (to be) given at the [Social Simulation Conference in Mainz, 23-27 September 2019](https://ssc2019.uni-mainz.de/). The paper presented covers the difficult question of making predictions with agent-based models. This NetLogo model allows an assessment of predictability (using categories defined in the paper) of [elementary cellular automata](https://en.wikipedia.org/wiki/Elementary_cellular_automaton) with ranges of rules encoded using Wolfram coding. Since the rules in a decimal sequence aren't really related to each other very well, this is rather a naive approach to have taken, but it demonstrates the principle that uncertainty about transition rules doesn't necessarily translate into full unpredictability.

# PredictionCA2.nlogo

Adjustments made to `PredictionCA.nlogo` to upgrade it. See the `info` tab for details, but the main upgrades mean there is a more explicit data input to the process of trying to find the rule, and a genetic algorithm option to search for the rule when there are too many options to search exhaustively.

# PredictionCA2.2.nlogo and version-spaces.R

Version of `PredictionCA2.nlogo` used in [a paper in JASSS](http://jasss.soc.surrey.ac.uk/24/3/2.html) to generate figures 3 and 4. To regenerate something like figure 4, rerun the experiment named `data-version-space` and then use `version-spaces.R` (which assumes the results of the `data-version-space` experiment are saved as `PredictionCA2.2_data-version-space-table.csv` in Netlogo's `table` format) to create the diagram -- it will be saved as `version-space-results.pdf`.
