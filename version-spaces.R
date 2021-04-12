#!/usr/bin/env Rscript
require(lattice)

data <- read.csv("PredictionCA2.2_data-version-space-table.csv", skip = 6)

m <- matrix(data = 0, nrow = 8, ncol = 40)
for(i in 1:40) for(j in 1:8) m[j, i] = nrow(subset(data, max.data == i & n.eliminated == c[j]))

pdf("version-space-results.pdf")
levelplot(t(m), xlab = "max-data", ylab = "n-eliminated", colorkey = list(space = "top"))
dev.off()
