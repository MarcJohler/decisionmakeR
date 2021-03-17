col_number <- 25
row_number <- 40
sample_size <- 10
nutzen <- matrix(sample(0:sample_size, size = col_number * row_number, replace = TRUE), ncol = col_number, nrow = row_number, byrow = TRUE)
sample_size <- sample(1:(col_number * row_number), 1)

sample_i <- sample(1:row_number, sample_size, replace = TRUE)
sample_j <- sample(1:col_number, sample_size, replace = TRUE)
sample_ij <- paste(sample_i, sample_j) %>% unique()

library(stringr)
adapt_i <- str_extract(sample_ij, pattern = "[:digit:]+") %>% as.integer()
adapt_j <- str_extract(sample_ij, pattern = "[:digit:]+$") %>% as.integer()

for (k in 1:length(sample_ij)) {
  nutzen[adapt_i[k], adapt_j[k]] <- round(runif(1, 0, 2) * nutzen[adapt_i[k], adapt_j[k]])
}

test_no <- ncol(nutzen)
it_bound <- matrix(c(0, 1), nrow = test_no, ncol = 2, byrow = TRUE)
for (j in 1:test_no) {
  it_bound[j, 2] <- sample(c(runif(1, 1 / test_no, 1), 1), 1)
  it_bound[j, 1] <- sample(c(runif(1, 0, min(it_bound[j, 2], 1 / test_no)), 0), 1)
}

ordinal_struc <- NULL
ordinal_size <- sample(2:test_no, size = 1)
ordinal_struc <- list(sample(1:test_no, ordinal_size))

library(microbenchmark)
microbenchmark(m_maximality(nutzen,
  method = "ep",
  ordinal_structure = ordinal_struc,
  boundaries = it_bound
),
m_maximality(nutzen,
  method = "lp",
  ordinal_structure = ordinal_struc,
  boundaries = it_bound
),
m_maximality(nutzen,
  method = "lppar",
  ordinal_structure = ordinal_struc,
  boundaries = it_bound
),
times = 1
)
