########
# Application example 1 - adapted from Jansen, Quantifying degrees of e-admissibility in decsion making with imprecise probabilities

nutzen_matrix <- rbind(
  c(37, 25, 23, 73, 91),
  c(50, 67, 2, 44, 94),
  c(60, 4, 96, 1, 83),
  c(16, 24, 31, 26, 100),
  c(3, 86, 76, 85, 11),
  c(12, 49, 66, 56, 14),
  c(39, 10, 92, 88, 57),
  c(62, 52, 80, 71, 42),
  c(90, 8, 74, 70, 38),
  c(63, 68, 36, 69, 9)
)
boundaries_example <- cbind(
  c(0.1, 0.05, 0.1, 0.2, 0.15),
  c(0.3, 0.1, 0.2, 0.4, 0.2)
)

# detect non-randomized Maxi-Min acts
gamma_maximin(nutzen_matrix, randomized_acts = FALSE, boundaries = boundaries_example, mode = "utility")

# detect E-admissible acts
e_admissibility(nutzen_matrix, filter_strategy = c("m-maximal", "admissible"), boundaries = boundaries_example)

# detect M-maximal acts
m_maximality(nutzen_matrix, method = "ep", filter_admissible = TRUE, boundaries = boundaries_example)

# detect E-epsilon-admissible acts for different epsilon values
e_epsilon_admissibility(nutzen_matrix, filter_strategy = c("m-maximal", "admissible"), boundaries = boundaries_example, epsilon = 0.005)
e_epsilon_admissibility(nutzen_matrix, filter_strategy = c("admissible", "e-admissible"), boundaries = boundaries_example, epsilon = 0.01)

# compute E-admissible-Extent for the E-admissible acts
e_admissibility_extent(nutzen_matrix, boundaries = boundaries_example, measure = "maximal")
e_admissibility_extent(nutzen_matrix, boundaries = boundaries_example, measure = "uniform")

# compute Joint Statistical Preference (only consider minimal dominance probability) and Joint Stochastic Dominance optimal acts
statistical_preference(nutzen_matrix, mode2 = "joint", optimism = 0, boundaries = boundaries_example, filter_admissible = TRUE)
stochastic_dominance(nutzen_matrix, boundaries = boundaries_example, filter_admissible = TRUE)

########
# Application example 2 - adapted from Jansen, Concepts for decision making under severe uncertainty with partial ordinal and partial cardinal preferences

# define relations like in the example
r1_strict <- list(c(1.2, 2.1, 2.2, 1.1))
r2_strict <- list(c(1.2, 2.2, 2.1, 1.1))

# check induced preference system for consistency
check_preference_system(2, 2, r1_strict = r1_strict, r2_strict = r2_strict)

# compute generalized interval expectation
generalized_interval_expectation(2, 2, r1_strict = r1_strict, r2_strict = r2_strict, delta = 0.25, ordinal_structure = list(c(2, 1)))

# detect global admissible acts
ps_global_admissibility(2, 2, r1_strict = r1_strict, r2_strict = r2_strict, mode = "utility", mode2 = "AM", ordinal_structure = list(c(2, 1)))
ps_global_admissibility(2, 2, r1_strict = r1_strict, r2_strict = r2_strict, mode = "utility", mode2 = "A", ordinal_structure = list(c(2, 1)))
ps_global_admissibility(2, 2, r1_strict = r1_strict, r2_strict = r2_strict, mode = "utility", mode2 = "M", ordinal_structure = list(c(2, 1)))
ps_global_admissibility(2, 2, r1_strict = r1_strict, r2_strict = r2_strict, mode = "utility", mode2 = "dominant", ordinal_structure = list(c(2, 1)))

# apply other criteria on the example
example_interval <- generalized_interval_expectation(2, 2, r1_strict = r1_strict, r2_strict = r2_strict, delta = 0.1, ordinal_structure = list(c(2, 1)))
# D_delta_maximin
hurwicz(example_interval, optimism = 0, randomized_acts = FALSE)
# D_delta_maximax
hurwicz(example_interval, optimism = 1, randomized_acts = FALSE)
# D_delta_maximix
hurwicz(example_interval, optimism = 0.4, randomized_acts = FALSE)
