# define utility matrix

utility <- rbind(c(5, 3, 2),
                 c(1, 6, 3),
                 c(2, 4, 0),
                 c(1, 3, 0))

boundaries <- rbind(c(0, 0.5),
                    c(0.2, 0.4),
                    c(0.25, 1))

ordinal_structure <- list(c(1,3))

# check if constructor works
decision_1 <- DecisionSystem$new(table = utility,
                                 interval_probabilities = boundaries,
                                 ordinal_relationships = ordinal_structure,
                                 mode = "utility")

# define probabilistic information


# call M-Maximality-function 

m_maximality(utility, 
             mode = "utility", 
             method = "lp", # use linear programming method
             filter_admissible = TRUE, # only consider admissible acts
             ordinal_structure = ordinal_structure, 
             boundaries = boundaries)


