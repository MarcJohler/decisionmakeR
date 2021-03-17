######## input check functions ########

# function to print interval structure as hint for the user if the
# 'interval_probabilities' input variable is not valid
interval_structure_error <- function(number_of_states) {
  message("'interval_probabilities' must have the following structure:")
  interval_structure <- matrix(c(
    paste("lower_boundary", 1:number_of_states, sep = ""),
    paste("upper_boundary", 1:number_of_states, sep = "")
  ), number_of_states, 2)
  row.names(interval_structure) <- 1:number_of_states
  print(head(interval_structure, max(5, min(number_of_states, 6 - (number_of_states - 6)))))
  if (number_of_states > 6) {
    message("...")
    rest <- interval_structure[-(1:(nrow(interval_structure) - 2)), ]
    row.names(rest) <- (number_of_states - 1):number_of_states
    print(rest)
  }
}

# check of probabilistic information
check_probability_consistency <- function(number_of_states, a1, a2, b1, b2,
                                          interval_probabilities, ordinal_relationships) {
  # check requirements for 'a1', 'a2', 'b1', 'b2'
  # for further information see rcdd documentation (function 'makeH')
  if (!is.null(a1)) {
    checkmate::assert_matrix(a1, ncols = number_of_states, any.missing = FALSE)
    checkmate::assert_numeric(a1)
    if (is.null(b1)) {
      # a1 only works together with b1 (see rcdd documentation)
      stop("please specify 'b1'")
    }
  }

  if (!is.null(a2)) {
    checkmate::assert_matrix(a2, ncols = number_of_states, any.missing = FALSE)
    checkmate::assert_numeric(a2)
    if (is.null(b2)) {
      # a2 only works together with b2 (see rcdd documentation)
      stop("please specify 'b2'")
    }
  }

  if (!is.null(b1)) {
    if (is.null(a1)) {
      stop("please specify 'a1'")
    }
    checkmate::assert(checkmate::check_numeric(b1, any.missing = FALSE),
      checkmate::check_atomic_vector(b1, len = nrow(a1)),
      combine = "and"
    )
  }

  if (!is.null(b2)) {
    if (is.null(a2)) {
      stop("please specify 'a2'")
    }
    checkmate::assert(checkmate::check_numeric(b2, any.missing = FALSE),
      checkmate::check_atomic_vector(b2, len = nrow(a1)),
      combine = "and"
    )
  }

  # check requirements for 'ordinal_relationships' if it is defined
  if (!is.null(ordinal_relationships)) {
    checkmate::assert_list(ordinal_relationships, any.missing = FALSE)
    for (i in seq_len(length(ordinal_relationships))) {
      checkmate::assert_atomic_vector(ordinal_relationships[[i]],
        any.missing = FALSE, min.len = 2
      )
      checkmate::assert_integerish(ordinal_relationships[[i]],
        lower = 1, upper = number_of_states
      )
    }
  }

  # check requirements on interval_probabilities
  if (!(is.matrix(interval_probabilities) && is.numeric(interval_probabilities))) {
    message("Error: 'interval_probabilities' is not a numeric matrix")
    interval_structure_error(number_of_states)
    stop("please redefine 'interval_probabilities'")
  }
  else if (any(dim(interval_probabilities) != c(number_of_states, 2))) {
    message(paste(
      "Error: 'interval_probabilities' has the wrong dimensions - dim(interval_probabilities) must equal",
      number_of_states, "2"
    ))
    interval_structure_error(number_of_states)
    stop("please redefine 'interval_probabilities'")
  }
  else if (sum(interval_probabilities[, 1]) > 1) {
    message("Error: sum of lower boundaries exceeds 1")
    interval_structure_error(number_of_states)
    message("it must hold that sum of lower boundaries is smaller than or equal to 1")
    stop("please redefine 'interval_probabilities'")
  }
  else if (sum(interval_probabilities[, 2]) < 1) {
    message("Error: upper boundaries don't conver a probability space")
    interval_structure_error(number_of_states)
    message("it must hold that sum of upper boundaries is greater than or equal to 1")
    stop("please redefine 'interval_probabilities'")
  }
  warning_reminder <- FALSE
  for (i in seq_len(nrow(interval_probabilities))) {
    if (interval_probabilities[i, 1] > interval_probabilities[i, 2]) {
      message(paste("Error: boundaries of state", i, "have been specified incorrectly"))
      interval_structure_error(number_of_states)
      message(paste(
        "State: ", i,
        ": it must hold that the lower boundary is smaller than or equal to the upper boundary"
      ))
      stop("please redefine 'interval_probabilities'")
    }
    else if (interval_probabilities[i, 1] < 0 || interval_probabilities[i, 1] > 1 ||
      interval_probabilities[i, 2] < 0 || interval_probabilities[i, 2] > 1) {
      message(paste("Error: boundaries of state", i, "have been specified incorrectly"))
      interval_structure_error(number_of_states)
      message(paste("it must hold that all values are element of the interval [0, 1]"))
      stop("please redefine 'interval_probabilities'")
    }
    if (interval_probabilities[i, 2] == 0) {
      warning_reminder <- TRUE
    }
  }
  if (warning_reminder) {
    warning("There is at least one state with upper probability of zero - priori might be degenerated")
  }

  ordinal_matrix <- diag(1, nrow = number_of_states, ncol = number_of_states)

  # transform 'ordinal_relationships' to a matrix so that [x, y] = 1 if
  # '...,x,y,...' is contained in at least one vector of 'ordinal_relationships'
  if (!is.null(ordinal_relationships)) {
    for (a in seq_len(length(ordinal_relationships))) {
      ordinal_vector <- ordinal_relationships[[a]]
      for (k in seq_len(length(ordinal_vector) - 1)) {
        ordinal_matrix[ordinal_vector[k], ordinal_vector[(k + 1):length(ordinal_vector)]] <- 1
      }
    }
  }

  # apply transitivity of state dominance, so that [x,y] = 1 if and only if p(x) >= p(y)
  # this may seem inefficient but it's necessary so that transitivity will be applied completely
  for (i in seq_len(number_of_states)) {
    for (j in seq_len(number_of_states)) {
      if (ordinal_matrix[i, j] > 0) {
        ordinal_matrix[i, ] <- ordinal_matrix[i, ] + ordinal_matrix[j, ]
      }
      else if (ordinal_matrix[j, i] > 0) {
        ordinal_matrix[j, ] <- ordinal_matrix[j, ] + ordinal_matrix[i, ]
      }
    }
  }
  # transform it to a binary relation again
  ordinal_matrix <- sign(ordinal_matrix)

  # define lower boundaries by applying transitivity for each dominated state
  for (i in seq_len(number_of_states)) {

    # for computational reasons let say that a state will always dominate itself
    ordinal_matrix[i, i] <- 1

    if (sum(ordinal_matrix[i, ]) == number_of_states) {
      # if the state dominates all of the other states, the lower boundary is either given by:

      # 1 divided through the number of all states ...
      tmp <- 1 / number_of_states

      # ... or by the maximal lower boundary of all states ...
      max <- max(interval_probabilities[, 1])

      # ... depending on what is larger
      if (tmp > max) {
        interval_probabilities[i, 1] <- tmp
      }
      else {
        interval_probabilities[i, 1] <- max
      }
    }
    else {
      # otherwise the lower boundary will be changed to the highest lower boundary of any state dominated by the corresponding state
      tmp <- max(interval_probabilities[as.logical(ordinal_matrix[i, ]), 1])
      if (tmp > interval_probabilities[i, 1]) {
        interval_probabilities[i, 1] <- tmp
      }
    }
  }

  states_order <- (1:number_of_states)[order(rowSums(ordinal_matrix), decreasing = TRUE)]

  # define upper boundaries (pre-sorting is necessary because dominators' boundaries will have an impact)
  # note that the upper boundaries will be too wide, since the computation of the actual boundaries is quite difficult
  for (i in states_order) {

    # compute all of the states which dominate the corresponding state
    dominators <- as.logical(ordinal_matrix[, i])

    if (length(dominators) != 0) {
      # the upper boundary is defined by the minimal upper boundary of the dominating states
      tmp <- min(interval_probabilities[dominators, 2])
    }
    else {
      tmp <- 1
    }

    # OR 1 minus the sum of the lower boundaries of all other states
    tmp2 <- 1 - sum(interval_probabilities[-i, 1])

    # the minimum will define the upper boundary
    tmp <- min(tmp, tmp2)
    if (tmp < interval_probabilities[i, 2]) {
      interval_probabilities[i, 2] <- tmp
    }
  }

  # if the lower boundaries sum up to 1 there is only one solution
  if (sum(interval_probabilities[, 1]) == 1) {
    return(rbind(interval_probabilities[, 1]))
  }

  # find logically induced lower boundaries
  for (i in seq_len(number_of_states)) {
    max_without_i <- sum(interval_probabilities[-i, 2])
    if (max_without_i < 1) {
      if (interval_probabilities[i, 1] < 1 - max_without_i) {
        interval_probabilities[i, 1] <- 1 - max_without_i
      }
    }
  }

  # check further requirments on 'interval_probabilities'
  # the sum of the lower boundaries must be maximal 1 and the sum of the upper boundaries must be minimal 1
  if ((round(sum(interval_probabilities[, 1]), 10) > 1) ||
    (round(sum(interval_probabilities[, 2]), 10) < 1)) {
    stop("'ordinal_relationships' and 'interval_probabilities' contain contradictory requirements")
  }

  for (i in seq_len(number_of_states)) {
    # no state may have an upper boundary higher than its lower boundary
    if (round(interval_probabilities[i, 1], 10) >
      round(interval_probabilities[i, 2], 10)) {
      stop("'ordinal_relationships' and 'interval_probabilities' contain contradictory requirements")
    }
    dominated <- (1:number_of_states)[(ordinal_matrix - diag(number_of_states, number_of_states))[i, ] == 1]
    # dominated states are not supposed to have a higher boundary value than their dominator
    for (j in dominated) {
      if (interval_probabilities[i, 1] < interval_probabilities[j, 1] ||
        interval_probabilities[i, 2] < interval_probabilities[j, 2]) {
        stop("'ordinal_relationships' and 'interval_probabilities' contain contradictory requirements")
      }
    }
  }

  if (warning_reminder == FALSE) {
    # if there is a state with upper boundary of 0, give a warning to the user
    for (i in seq_len(nrow(interval_probabilities))) {
      if (interval_probabilities[i, 2] == 0) {
        warning("There is at least one state with upper probability of zero - priori might be degenerated")
        break
      }
    }
  }
  return(interval_probabilities)
}


# R6-class for Decision Systems
DecisionSystem <- R6::R6Class("DecisionSystem",
  private = list(
    .table = NA,
    .mode = NA,
    .interval_probabilities = NA,
    .ordinal_relationships = NA,
    .a1 = NA,
    .b1 = NA,
    .a2 = NA,
    .b2 = NA,
    .only_admissible = NA
  ),
  public = list(
    initialize = function(table, mode = c("utility", "loss"),
                          interval_probabilities = matrix(c(0, 1), nrow = ncol(table), ncol = 2, byrow = TRUE),
                          ordinal_relationships = NULL,
                          a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL,
                          check_admissibility = TRUE) {

      # check 'table' to be a non-trivial utility/loss
      # table with no missing values
      checkmate::assert_matrix(table, min.rows = 2, min.cols = 2)
      checkmate::assert_numeric(table, any.missing = FALSE)
      # check 'mode' to be one of the valid options
      mode <- match.arg(mode)
      # check if 'check_admissibility' is a logical value
      checkmate::assert_flag(check_admissibility)
      # check consistency of information on probabilities
      interval_probabilities <- check_probability_consistency(
        ncol(table),
        a1, b1, a2, b2,
        interval_probabilities,
        ordinal_relationships
      )
      # safe values in object
      private$.table <- table
      private$.mode <- mode
      private$.interval_probabilities <- interval_probabilities
      private$.ordinal_relationships <- ordinal_relationships
      private$.a1 <- a1
      private$.b1 <- b1
      private$.a2 <- a2
      private$.b2 <- b2
      private$.only_admissible <- check_admissibility
      # if 'check_admissibility' is set to TRUE, apply algorithm to exclude
      # dominated acts
      if (check_admissibility) {
        self$exclude_dominated()
      }
    },
    # method to show/print the class
    show = function() {
      list(table = private$.table,
           mode = private$.mode,
           interval_probabilites = private$.interval_probabilities,
           ordinal_relationships = private$.ordinal_relationships,
           a1 = private$.a1,
           b1 = private$.b1,
           a2 = private$.a2,
           b2 = private$.b2,
           only_admisslbe = private$.only_admissible)
    },
    # method to exclude strictly dominated acts
    exclude_dominated = function(strong_domination = FALSE,
                                 exclude_duplicates = FALSE,
                                 column_presort = FALSE) {
      #' strong_domination', 'column_presort' and 'exclude_duplicates'
      # must be single logical values
      checkmate::assert_flag(strong_domination)
      if (strong_domination == TRUE) {
        checkmate::assert_flag(exclude_duplicates, null.ok = TRUE)
      }
      else {
        checkmate::assert_flag(exclude_duplicates)
      }
      checkmate::assert_flag(column_presort)

      # if there is only one possible act, that act is of course admissible
      if (nrow(private$.table) == 1) {
        return(invisible(NULL))
      }

      # copy 'table' attribute into local storage
      table <- private$.table

      number_of_states <- ncol(table)
      number_of_acts <- nrow(table)

      # Sort acts to be more likely to be dominated to be in the lower rows
      # Acts cannot be dominated by acts with lower row sums
      row_sums <- data.frame(
        indx = 1:number_of_acts,
        rowSum = rowSums(table)
      )
      row_sums <- row_sums[order(row_sums$rowSum,
        decreasing = switch(private$.mode,
          "utility" = TRUE,
          "loss" = FALSE
        )
      ), ]
      row_sums <- row_sums[["indx"]]
      # Sort states to be selected earlier when higher rows have low values
      # (optional; does not always lead to faster processing)
      if (column_presort) {
        weighted_table <- table

        # normalize the utility for each state (column)
        for (j in seq_len(number_of_states)) {
          weighted_table[, j] <- (weighted_table[, j] - min(weighted_table[, j]))
          weighted_table[, j] <- weighted_table[, j] / (max(weighted_table[, j]))
        }

        # calculate score values used for ordering the columns in a advantageous way for the detection of admissibility
        weights <- seq(number_of_acts - 1, 0)
        weighted_table <- weights * weighted_table / sum(weights)
        weighted_table_colSums <- colSums(weighted_table)

        table <- table[, order(weighted_table_colSums,
          decreasing = switch(private$.mode,
            "utility" = FALSE,
            "loss" = TRUE
          )
        )]
      }

      # algorithm for admissible acts according to strong dominance
      if (strong_domination == TRUE) {
        if (private$.mode == "utility") {
          i <- 1
          while (i < length(row_sums)) {
            j <- i + 1
            while (j <= length(row_sums)) {
              # reminder saves if there is a state for which act j performs better than or at least as good as act i
              reminder <- FALSE
              for (k in seq_len(number_of_states)) {
                if (table[row_sums[j], k] >= table[row_sums[i], k]) {
                  reminder <- TRUE
                  break
                }
              }
              if (reminder == FALSE) {
                # if reminder is FALSE at the end of the loop, act j is strongly dominated by act i
                row_sums <- row_sums[-j]
                j <- j - 1
              }
              j <- j + 1
            }
            i <- i + 1
          }
        }
        else if (private$.mode == "loss") {
          i <- 1
          while (i < length(row_sums)) {
            j <- i + 1
            while (j <= length(row_sums)) {
              reminder <- FALSE
              for (k in seq_len(number_of_states)) {
                if (table[row_sums[j], k] <= table[row_sums[i], k]) {
                  reminder <- TRUE
                  break
                }
              }
              if (reminder == FALSE) {
                row_sums <- row_sums[-j]
                j <- j - 1
              }
              j <- j + 1
            }
            i <- i + 1
          }
        }
      }
      else {
        if (exclude_duplicates == FALSE) {
          # algorithm for admissible acts according to strict dominance
          if (private$.mode == "utility") {
            i <- 1
            while (i < length(row_sums)) {
              j <- i + 1
              while (j <= length(row_sums)) {
                # in addition to saving if act j has been better than act i in at least one state, one also has to save if the opposite happened
                reminder_equal <- TRUE
                reminder <- FALSE
                for (k in seq_len(number_of_states)) {
                  if (table[row_sums[j], k] > table[row_sums[i], k]) {
                    reminder <- TRUE
                    break
                  }
                  else if (table[row_sums[j], k] < table[row_sums[i], k]) {
                    reminder_equal <- FALSE
                  }
                }
                # if act j has not been better than act i in any state and act i has been better than act j in any state, act j is strictly dominated by act i
                if (reminder == FALSE) {
                  if (reminder_equal == FALSE) {
                    row_sums <- row_sums[-j]
                    j <- j - 1
                  }
                }
                j <- j + 1
              }
              i <- i + 1
            }
          }
          else if (private$.mode == "loss") {
            i <- 1
            while (i < length(row_sums)) {
              j <- i + 1
              while (j <= length(row_sums)) {
                reminder_equal <- TRUE
                reminder <- FALSE
                for (k in seq_len(number_of_states)) {
                  if (table[row_sums[j], k] < table[row_sums[i], k]) {
                    reminder <- TRUE
                    break
                  }
                  else if (table[row_sums[j], k] > table[row_sums[i], k]) {
                    reminder_equal <- FALSE
                  }
                }
                if (reminder == FALSE) {
                  if (reminder_equal == FALSE) {
                    row_sums <- row_sums[-j]
                    j <- j - 1
                  }
                }
                j <- j + 1
              }
              i <- i + 1
            }
          }
        }
        else if (exclude_duplicates == TRUE) {
          # algorithm for admissible acts according to weak dominance (only one duplicate will remain)
          if (private$.mode == "utility") {
            i <- 1
            while (i < length(row_sums)) {
              j <- i + 1
              while (j <= length(row_sums)) {
                # remember if act j has been better than act i in at least one state
                reminder <- FALSE
                for (k in seq_len(number_of_states)) {
                  if (table[row_sums[j], k] > table[row_sums[i], k]) {
                    reminder <- TRUE
                    break
                  }
                }
                # if act j has not been better than act i in any state, act j will be excluded (could be equivalent to act i)
                if (reminder == FALSE) {
                  row_sums <- row_sums[-j]
                  j <- j - 1
                }
                j <- j + 1
              }
              i <- i + 1
            }
          }
          else if (private$.mode == "loss") {
            i <- 1
            while (i < length(row_sums)) {
              j <- i + 1
              while (j <= length(row_sums)) {
                reminder <- FALSE
                for (k in seq_len(number_of_states)) {
                  if (table[row_sums[j], k] < table[row_sums[i], k]) {
                    reminder <- TRUE
                    break
                  }
                }
                if (reminder == FALSE) {
                  row_sums <- row_sums[-j]
                  j <- j - 1
                }
                j <- j + 1
              }
              i <- i + 1
            }
          }
        }
      }
      private$.table <- table[row_sums, ]
      return(invisible(NULL))
    }
  ),
  active = list(
    table = function() {
      private$.table
    },
    mode = function() {
      private$.mode
    },
    a1 = function() {
      private$.a1
    },
    b1 = function() {
      private$.b1
    },
    a2 = function() {
      private$.a2
    },
    b2 = function() {
      private$.b2
    },
    interval_probabilities = function() {
      private$.interval_probabilities
    },
    ordinal_relationships = function() {
      private$.ordinal_relationships
    },
    only_admissible = function() {
      private$.only_admissible
    }
  )
)
