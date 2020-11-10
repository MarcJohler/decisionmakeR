# required packages

library(tidyverse)
library(lpSolve)
library(rcdd)
library(checkmate)

######## input check functions ########

#function to print boundary structure as hint for the user
boundary_structure_error <- function(number_of_states){
  message("'boundaries' must have the following structure:")
  boundaries_structure <- matrix(c(paste("lower_boundary", 1:number_of_states, sep = ""), paste("upper_boundary", 1:number_of_states, sep = "")), number_of_states, 2)
  row.names(boundaries_structure) <- 1:number_of_states
  print(head(boundaries_structure, max(5, min(number_of_states, 6 - (number_of_states - 6)))))
  if (number_of_states > 6) {
    message("...")
    rest <- boundaries_structure[-(1:(nrow(boundaries_structure) - 2)), ]
    row.names(rest) <- (number_of_states - 1):number_of_states
    print(rest)
  }
}

#check of probabilistic information 
check_probability_consistency <- function(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure) {
  # check requirements for a1,a2,b1,b2
  # for further information see rcdd documentation (function 'makeH')
  if (!is.null(a1)) {
    assert_matrix(a1, ncols = number_of_states, any.missing = FALSE)
    assert_numeric(a1)
    if (is.null(b1)) {
      #a1 only works together with b1 (see rcdd documentation)
      stop("please specify 'b1'")
    }
  }
  
  if (!is.null(a2)) {
    assert_matrix(a2, ncols = number_of_states, any.missing = FALSE)
    assert_numeric(a2)
    if (is.null(b2)) {
      #a2 only works together with b2 (see rcdd documentation)
      stop("please specify 'b2'")
    }
  }
  
  if (!is.null(b1)) {
    if (is.null(a1)) {
      stop("please specify 'a1'")
    }
    assert(check_numeric(b1, any.missing = FALSE), 
           check_atomic_vector(b1, len = nrow(a1)),
           combine = "and"
    )
  }
  
  if (!is.null(b2)) {
    if (is.null(a2)) {
      stop("please specify 'a2'")
    }
    assert(check_numeric(b2, any.missing = FALSE), 
           check_atomic_vector(b2, len = nrow(a1)),
           combine = "and"
    )
  }
  
  # check requirements for ordinal_structure if it is defined
  if (!is.null(ordinal_structure)) {
    assert_list(ordinal_structure, any.missing = FALSE)
    for (i in 1:length(ordinal_structure)) {
      assert_atomic_vector(ordinal_structure[[i]], any.missing = FALSE, min.len = 2)
      assert_integerish(ordinal_structure[[i]], lower = 1, upper = number_of_states)
    }
  }
  
  # check requirements on boundaries
  if (!(is.matrix(boundaries) && is.numeric(boundaries))) {
    message("Error: 'boundaries' is not a numeric matrix")
    boundary_structure_error(number_of_states)
    stop("please redefine 'boundaries'")
  }
  else if (any(dim(boundaries) != c(number_of_states, 2))) {
    message(paste("Error: 'boundaries' has the wrong dimensions - dim(boundaries) must equal", number_of_states, "2"))
    boundary_structure_error(number_of_states)
    stop("please redefine 'boundaries'")
  }
  else if (sum(boundaries[, 1]) > 1) {
    message("Error: sum of lower boundaries exceeds 1")
    boundary_structure_error(number_of_states)
    message("it must hold that sum of lower boundaries is smaller than or equal to 1")
    stop("please redefine 'boundaries'")
  }
  else if (sum(boundaries[, 2]) < 1) {
    message("Error: upper boundaries don't conver a probability space")
    boundary_structure_error(number_of_states)
    message("it must hold that sum of upper boundaries is greater than or equal to 1")
    stop("please redefine 'boundaries'")
  }
  warning_reminder <- FALSE
  for (i in 1:nrow(boundaries)) {
    if (boundaries[i, 1] > boundaries[i, 2]) {
      message(paste("Error: boundaries of state", i, "have been specified incorrectly"))
      boundary_structure_error(number_of_states)
      message(paste("it must hold that lower_boundary", i, "is smaller than or equal to upper_boundary", i))
      stop("please redefine 'boundaries'")
    }
    else if (boundaries[i, 1] < 0 || boundaries[i, 1] > 1 || boundaries[i, 2] < 0 || boundaries[i, 2] > 1) {
      message(paste("Error: boundaries of state", i, "have been specified incorrectly"))
      boundary_structure_error(number_of_states)
      message(paste("it must hold that all values are element of the interval [0,1]"))
      stop("please redefine 'boundaries'")
    }
    if (boundaries[i, 2] == 0) {
      warning_reminder <- TRUE
    }
  }
  if (warning_reminder) {
    warning("There is at least one state with upper probability of zero - priori might be degenerated")
  }
  
  ordinal_matrix <- diag(1, nrow = number_of_states, ncol = number_of_states)
  
  # transform ordinal_structure to a matrix so that [x,y] = 1 if '...,x,y,...' is contained in at least one vector of 'ordinal_structure' 
  if (!is.null(ordinal_structure)) {
    for (a in 1:length(ordinal_structure)) {
      ordinal_vector <- ordinal_structure[[a]]
      for (k in (1:(length(ordinal_vector) - 1))) {
        ordinal_matrix[ordinal_vector[k], ordinal_vector[(k + 1):length(ordinal_vector)]] <- 1
      }
    }
  }
  
  # apply transitivity of state dominance, so that [x,y] = 1 if and only if p(x) >= p(y)
  # this may seem inefficient but it's necessary so that transitivity will be applied completely 
  for (i in 1:number_of_states) {
    for (j in 1:number_of_states) {
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
  for (i in 1:number_of_states) {
    
    #for computational reasons let say that a state will always dominate itself
    ordinal_matrix[i, i] <- 1
    
    if (sum(ordinal_matrix[i, ]) == number_of_states) {
      # if the state dominates all of the other states, the lower boundary is either given by:
      
      # 1 divided through the number of all states ...
      tmp <- 1 / number_of_states
      
      # ... or by the maximal lower boundary of all states ...
      max <- max(boundaries[, 1])
      
      #... depending on what is larger
      if (tmp > max) {
        boundaries[i, 1] <- tmp
      }
      else {
        boundaries[i, 1] <- max
      }
    }
    else {
      #otherwise the lower boundary will be changed to the highest lower boundary of any state dominated by the corresponding state
      tmp <- max(boundaries[as.logical(ordinal_matrix[i, ]), 1])
      if (tmp > boundaries[i, 1]) {
        boundaries[i, 1] <- tmp
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
      tmp <- min(boundaries[dominators, 2])
    }
    else {
      tmp <- 1
    }
    
    # OR 1 minus the sum of the lower boundaries of all other states
    tmp2 <- 1 - sum(boundaries[-i, 1])
    
    # the minimum will define the upper boundary 
    tmp <- min(tmp, tmp2)
    if (tmp < boundaries[i, 2]) {
      boundaries[i, 2] <- tmp
    }
  }
  
  # if the lower boundaries sum up to 1 there is only one solution
  if (sum(boundaries[, 1]) == 1) {
    return(rbind(boundaries[, 1]))
  }
  
  # find logically induced lower boundaries
  for (i in 1:number_of_states) {
    max_without_i <- sum(boundaries[-i, 2])
    if (max_without_i < 1) {
      if (boundaries[i, 1] < 1 - max_without_i) {
        boundaries[i, 1] <- 1 - max_without_i
      }
    }
  }
  
  # check further requirments on boundaries
  # the sum of the lower boundaries must be maximal 1 and the sum of the upper boundaries must be minimal 1
  if ((round(sum(boundaries[, 1]), 10) > 1) || (round(sum(boundaries[, 2]), 10) < 1)) {
    stop("'ordinal_structure' and 'boundaries' contain contradictory requirements")
  }
  
  for (i in 1:number_of_states) {
    # no state may have an upper boundary higher than its lower boundary
    if (round(boundaries[i, 1], 10) > round(boundaries[i, 2], 10)) {
      stop("'ordinal_structure' and 'boundaries' contain contradictory requirements")
    }
    dominated <- (1:number_of_states)[(ordinal_matrix - diag(number_of_states, number_of_states))[i, ] == 1]
    # dominated states are not supposed to have a higher boundary value than their dominator
    for (j in dominated) {
      if (boundaries[i, 1] < boundaries[j, 1] || boundaries[i, 2] < boundaries[j, 2]) {
        stop("'ordinal_structure' and 'boundaries' contain contradictory requirements")
      }
    }
  }
  
  if (warning_reminder == FALSE) {
    # if there is a state with upper boundary of 0, give a warning to the user
    for (i in 1:nrow(boundaries)) {
      if (boundaries[i, 2] == 0) {
        warning("There is at least one state with upper probability of zero - priori might be degenerated")
        break
      }
    }
  }
  return(boundaries)
}

generate_probability_constraints <- function(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure) {
  # additional part because constraints from state probability requirements need to be included
  # first add indicators for the states to the a1-matrix
  # and their respective boundary to the b1-vector
  for (k in 1:nrow(boundaries)) {
    a1 <- rbind(a1, rep(0, number_of_states))
    a1[nrow(a1), k] <- 1
    b1 <- c(b1, boundaries[k, 2])
    a1 <- rbind(a1, rep(0, number_of_states))
    a1[nrow(a1), k] <- -1
    b1 <- c(b1, (-1) * boundaries[k, 1])
  }
  # then set indicators for the ordinal relations between states:
  # dominating state --> -1, dominated state --> 1
  # the corresponding entry in b1 will be 0
  if (!is.null(ordinal_structure)) {
    for (k in 1:length(ordinal_structure)) {
      current_order <- ordinal_structure[[k]]
      for (j in 1:(length(current_order) - 1)) {
        a1 <- rbind(a1, rep(0, number_of_states))
        a1[nrow(a1), current_order[j]] <- -1
        a1[nrow(a1), current_order[j + 1]] <- 1
        b1 <- c(b1, 0)
      }
    }
  }
  
  # the sum of the states probabilities must equal 1
  a2 <- rbind(a2, rep(1, number_of_states))
  b2 <- c(b2, 1)
  
  # checking for redundant constraints and excluding them
  hrep <- makeH(a1, b1, a2, b2, x = NULL)
  redundant_rows <- redundant(hrep)$redundant
  if (!is.null(redundant_rows)) {
    hrep <- hrep[-redundant_rows, ]
  }
  
  return(hrep)
}
  
#check of possible priori 
check_priori_requirements <- function(panel,priori){
  assert_atomic_vector(priori, len = ncol(panel))
  assert_numeric(priori, lower = 0, upper = 1)
  assert(sum(priori) == 1)
}

#check requirements on a 0-1 normalized parameter
check_normalized_parameter <- function(parameter){
  assert_number(parameter, lower = 0, upper = 1)
}

#check measures for preference systems
check_preference_measure <- function(number_of_acts, number_of_states, measure, type = c("cardinal","ordinal","binary")) {
  
  #type must be one of "cardinal","ordinal","binary"
  type <- match.arg(type)
  
  #the measure must be a data frame representing the utilty table in long format
  assert_data_frame(measure, nrows = number_of_acts * number_of_states)
  
  #cardinal and ordinal measures must be numeric data.frames
  if (type %in% c("cardinal","ordinal")) {
    for (j in 1:ncol(measure)) {
      if (!is.numeric(measure[, j])) {
        stop(paste("'There is at least one non-numeric column in ", measure))
      }
    }
  }
  else {#binary measures must be logical data.frames
    for (j in 1:ncol(measure)) {
      if (!is.logical(measure[, j])) {
        stop(paste("'There is at least one non-numeric column in ", measure))
      }
    }
  }
}

#check input data of a preference system
check_preference_relations <- function(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent) {
  
  # the number of acts and states must be represented by strictly positive integerish values
  assert_count(number_of_acts, positive = TRUE)
  assert_count(number_of_states, positive = TRUE)
  
  # necessary to calculate indices 
  state_factor <- 10^(floor(logb(number_of_states, 10)) + 1)
  
  #r1_strict must be a list of length >= 1
  assert_list(r1_strict, min.len = 1)
  
  for (i in 1:length(r1_strict)) {
    #each element of r1_strict must be a numerical vector of length >= 2 representing coordinates of a utility table
    vector_i <- r1_strict[[i]]
    assert_atomic_vector(vector_i, min.len = 2)
    assert_numeric(vector_i, lower = 1.1, upper = number_of_acts + number_of_states / state_factor)
    #for computational reasons there are no duplicates allowed 
    if (length(unique(vector_i)) != length(vector_i)) {
      stop("a vector of 'r1_strict' contains duplicates")
    }
    for (j in 1:length(vector_i)) {
      #this part is necessary to check every entry in r1_strict to fit the format A.S as a double value (A is an action, S a state)
      entry_j <- vector_i[j]
      state_indx <- round(entry_j %% 1 * state_factor, floor(logb(number_of_states, 10)) + 2)
      if (floor(entry_j) > number_of_acts || floor(entry_j) < 1) {
        stop("coordinates of r1_strict must have the format 'action.state'")
      }
      else if (state_indx > number_of_states || state_indx < 1) {
        stop("coordinates of r1_strict must have the format 'action.state'")
      }
    }
  }
  
  if (!is.null(r1_indifferent)) {  
    #r1_indifferent must be a list of length >= 1
    assert_list(r1_indifferent, min.len = 1)
    
    for (i in 1:length(r1_indifferent)) {
      #each element of r1_indifferent must be a numerical vector of length 4 representing coordinates of an utility table
      vector_i <- r1_indifferent[[i]]
      assert_atomic_vector(vector_i, len = 4)
      assert_numeric(vector_i, lower = 1.1, upper = number_of_acts + number_of_states / state_factor)
      # to avoid redundancies there is only one duplicate per vector allowed
      if (length(unique(vector_i)) < 3) {
        stop("a vector of 'r1_indifferent' contains redundant information")
      }
      for (j in 1:length(vector_i)) {
        entry_j <- vector_i[j]
        state_indx <- round(entry_j %% 1 * state_factor, floor(logb(number_of_states, 10)) + 2)
        #this part is necessary to check every entry in r1_strict to fit the format A.S as a double value (A is an action, S a state)
        if (floor(entry_j) > number_of_acts || floor(entry_j) < 1) {
          stop("coordinates of r1_indifferent must have the format 'action.state'")
        }
        if (state_indx > number_of_states || state_indx < 1) {
          stop("coordinates of r1_indifferent must have the format 'action.state'")
        }
      }
    }
  }
  
  #do the same for relation r2, but r2_strict is not obligatory like r1_strict
  if (!is.null(r2_strict)) {
    for (i in 1:length(r2_strict)) {
      vector_i <- r2_strict[[i]]
      assert_atomic_vector(vector_i, min.len = 2)
      assert_numeric(vector_i, lower = 1.1, upper = number_of_acts + number_of_states / state_factor)
      if (length(unique(vector_i)) < 3) {
        stop("a vector of 'r2_strict' contains redundant information")
      }
      for (j in 1:length(vector_i)) {
        entry_j <- vector_i[j]
        state_indx <- round(entry_j %% 1 * state_factor, floor(logb(number_of_states, 10)) + 2)
        if (floor(entry_j) > number_of_acts || floor(entry_j) < 1) {
          stop("coordinates of r2_strict must have the format 'action.state'")
        }
        else if (state_indx > number_of_states || state_indx < 1) {
          stop("coordinates of r2_strict must have the format 'action.state'")
        }
      }
    }
  }
  
  if (!is.null(r2_indifferent)) {  
    
    assert_list(r2_indifferent, min.len = 1)
    
    for (i in 1:length(r2_indifferent)) {
      vector_i <- r2_indifferent[[i]]
      assert_atomic_vector(vector_i, len = 4)
      assert_numeric(vector_i, lower = 1.1, upper = number_of_acts + number_of_states / state_factor)
      if (length(unique(vector_i)) < 3) {
        stop("a vector of 'r2_indifferent' contains redundant information")
      }
      for (j in 1:length(vector_i)) {
        entry_j <- vector_i[j]
        state_indx <- round(entry_j %% 1 * state_factor, floor(logb(number_of_states, 10)) + 2)
        if (floor(entry_j) > number_of_acts || floor(entry_j) < 1) {
          stop("coordinates of r2_indifferent must have the format 'action.state'")
        }
        if (state_indx > number_of_states || state_indx < 1) {
          stop("coordinates of r2_indifferent must have the format 'action.state'")
        }
      }
    }
  }
  return(state_factor)
}

######### functions for user #########
#### functions for classic decision theory based on utility table #####
exclude_dominated <- function(panel, mode = c("utility","loss"), strong_domination = FALSE, exclude_duplicates = FALSE, column_presort = FALSE) {
  
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  #'strong_domination', 'column_presort' and 'exclude_duplicates' must be single logical values
  assert_flag(strong_domination)
  if (strong_domination == TRUE) {
    assert_flag(exclude_duplicates, null.ok = TRUE)
  }
  else {
    assert_flag(exclude_duplicates)
  }
  
  assert_flag(column_presort)
  
  # if there is only one possible act, that act is of course admissible
  if (nrow(panel) == 1) {
    return(1)
  }
  
  number_of_states <- ncol(panel)
  number_of_acts <- nrow(panel)
  
  # Sort acts to be more likely to be dominated to be in the lower rows
  # Acts cannot be dominated by acts with lower row sums
  row_sums <- data.frame(indx = 1:number_of_acts, rowSum = rowSums(panel))
  if (mode == "utility") {
    row_sums <- row_sums[order(row_sums$rowSum, decreasing = TRUE), ]
    row_sums <- row_sums$indx
  }
  else if (mode == "loss") {
    row_sums <- row_sums[order(row_sums$rowSum, decreasing = FALSE), ]
    row_sums <- row_sums$indx
  }
  
  # Sort states to be selected earlier when higher rows have low values (optional; does not always lead to faster processing)
  if (column_presort) {
    weighted_panel <- panel
    
    #normalize the utility for each state (column)
    for (j in 1:number_of_states) {
      weighted_panel[, j] <- (weighted_panel[, j] - min(weighted_panel[, j]))
      weighted_panel[, j] <- weighted_panel[, j] / (max(weighted_panel[, j]))
    }
    
    #calculate score values used for ordering the columns in a advantageous way for the detection of admissibility
    weights <- ((number_of_acts - 1):0)
    weighted_panel <- weights * weighted_panel / sum(weights)
    weighted_panel_colSums <- colSums(weighted_panel)
    
    if (mode == "utility") {
      panel <- panel[, order(weighted_panel_colSums, decreasing = FALSE)]
    }
    if (mode == "loss") {
      panel <- panel[, order(weighted_panel_colSums, decreasing = TRUE)]
    }
  }
  
  # algorithm for admissible acts according to strong dominance
  if (strong_domination == TRUE) {
    if (mode == "utility") {
      i <- 1
      while (i < length(row_sums)) {
        j <- i + 1
        while (j <= length(row_sums)) {
          #reminder saves if there is a state for which act j performs better than or at least as good as act i 
          reminder <- FALSE
          for (k in 1:number_of_states) {
            if (panel[row_sums[j], k] >= panel[row_sums[i], k]) {
              reminder <- TRUE
              break
            }
          }
          if (reminder == FALSE) {
            #if reminder is FALSE at the end of the loop, act j is strongly dominated by act i 
            row_sums <- row_sums[-j]
            j <- j - 1
          }
          j <- j + 1
        }
        i <- i + 1
      }
    }
    else if (mode == "loss") {
      i <- 1
      while (i < length(row_sums)) {
        j <- i + 1
        while (j <= length(row_sums)) {
          reminder <- FALSE
          for (k in 1:number_of_states) {
            if (panel[row_sums[j], k] <= panel[row_sums[i], k]) {
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
      if (mode == "utility") {
        i <- 1
        while (i < length(row_sums)) {
          j <- i + 1
          while (j <= length(row_sums)) {
            #in addition to saving if act j has been better than act i in at least one state, one also has to save if the opposite happened 
            reminder_equal <- TRUE
            reminder <- FALSE
            for (k in 1:number_of_states) {
              if (panel[row_sums[j], k] > panel[row_sums[i], k]) {
                reminder <- TRUE
                break
              }
              else if (panel[row_sums[j], k] < panel[row_sums[i], k]) {
                reminder_equal <- FALSE
              }
            }
            #if act j has not been better than act i in any state and act i has been better than act j in any state, act j is strictly dominated by act i 
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
      else if (mode == "loss") {
        i <- 1
        while (i < length(row_sums)) {
          j <- i + 1
          while (j <= length(row_sums)) {
            reminder_equal <- TRUE
            reminder <- FALSE
            for (k in 1:number_of_states) {
              if (panel[row_sums[j], k] < panel[row_sums[i], k]) {
                reminder <- TRUE
                break
              }
              else if (panel[row_sums[j], k] > panel[row_sums[i], k]) {
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
      if (mode == "utility") {
        i <- 1
        while (i < length(row_sums)) {
          j <- i + 1
          while (j <= length(row_sums)) {
            #remember if act j has been better than act i in at least one state
            reminder <- FALSE
            for (k in 1:number_of_states) {
              if (panel[row_sums[j], k] > panel[row_sums[i], k]) {
                reminder <- TRUE
                break
              }
            }
            #if act j has not been better than act i in any state, act j will be excluded (could be equivalent to act i)
            if (reminder == FALSE) {
              row_sums <- row_sums[-j]
              j <- j - 1
            }
            j <- j + 1
          }
          i <- i + 1
        }
      }
      else if (mode == "loss") {
        i <- 1
        while (i < length(row_sums)) {
          j <- i + 1
          while (j <= length(row_sums)) {
            reminder <- FALSE
            for (k in 1:number_of_states) {
              if (panel[row_sums[j], k] < panel[row_sums[i], k]) {
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
  return(row_sums)
}

#function to compute the set of extreme points for imprecise probabilities
extreme_point_finder_rcdd <- function(number_of_states, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, boundaries = matrix(c(0, 1), nrow = number_of_states, ncol = 2, byrow = TRUE), ordinal_structure = NULL) {
  
  # check requirements for number_of_states
  assert_integerish(number_of_states, len = 1, lower = 2, any.missing = FALSE)
  
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # add requirements of boundaries and ordinal_structure to a1,b1,a2,b2
  for (i in 1:nrow(boundaries)) {
    a1 <- rbind(a1, rep(0, number_of_states))
    a1[nrow(a1), i] <- 1
    b1 <- c(b1, boundaries[i, 2])
    a1 <- rbind(a1, rep(0, number_of_states))
    a1[nrow(a1), i] <- -1
    b1 <- c(b1, (-1) * boundaries[i, 1])
  }
  
  if (!is.null(ordinal_structure)) {
    for (i in 1:length(ordinal_structure)) {
      current_order <- ordinal_structure[[i]]
      for (j in 1:(length(current_order) - 1)) {
        a1 <- rbind(a1, rep(0, number_of_states))
        a1[nrow(a1), current_order[j]] <- -1
        a1[nrow(a1), current_order[j + 1]] <- 1
        b1 <- c(b1, 0)
      }
    }
  }
  
  a2 <- rbind(a2, rep(1, number_of_states))
  b2 <- c(b2, 1)
  
  # redundant constraints can be excluded
  hrep <- makeH(a1, b1, a2, b2, x = NULL)
  redundant_rows <- redundant(hrep)$redundant
  if (!is.null(redundant_rows)) {
    hrep <- hrep[-redundant_rows, ]
  }
  
  # package rcdd takes care of the rest
  if (validcdd(hrep)) {
    vrep <- scdd(d2q(hrep), representation = "H")$output
    vrep <- q2d(vrep[, -c(1, 2)])
    
    # check if there is a feasible solution
    if (nrow(vrep) == 0) {
      stop("There is no feasible solution")
    }
    else {
      return(vrep)
    }
  }
}

# function to compute the M-maximal acts through an own approach based on extreme points
m_maximality_ep <- function(utility_table,  mode = c("utility","loss"), a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(utility_table), ncol = 2, byrow = TRUE)) {
  number_of_states <- ncol(utility_table)
  
  # first compute the extreme points and the utility for each act and extreme point
  extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
  expected_utility <- utility_table %*% t(extreme_points)
  
  # detect admissibility in accord to strong dominance
  output_ind <- exclude_dominated(expected_utility, mode, TRUE)
  output <- rbind(utility_table[output_ind, ])
  row.names(output) <- row.names(expected_utility)[output_ind]
  return(output)
}

# function to compute the M-maximal acts through linear optimization
m_maximality_lp <- function(utility_table,  mode = c("utility","loss"), a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(utility_table), ncol = 2, byrow = TRUE)) {
  number_of_states <- ncol(utility_table)
  
  # since detecting E-admissibility is faster than detecting M-maximality one can exclude these acts before starting
  e_admissible_acts <- e_admissibility(utility_table, mode, "none", a1, b1, a2, b2, ordinal_structure, boundaries)
  e_admissible_indices <- row.names(e_admissible_acts) %>% as.integer()
  
  m_maximal <- c()
  number_of_acts <- nrow(utility_table)
  number_of_states <- ncol(utility_table)
  
  for (i in setdiff(1:number_of_acts, e_admissible_indices)) {
    # constraints for comparing distinct acts and to bind the sum of states' probabilities to a maximum of 1
    if (mode == "utility") {
      constr_dir <- rep(c("<=", "<="), number_of_acts - 1)
    }
    else if (mode == "loss") {
      constr_dir <- rep(c(">=", "<="), number_of_acts - 1)
    }
    constr_mat <- matrix(0, 2 * (number_of_acts - 1), (number_of_acts - 1) * number_of_states)
    number_of_var <- ncol(constr_mat)
    utility_table_woi <- rbind(utility_table[-i, ])
    utility_table_i <- rbind(utility_table[i, ])
    for (j in 1:(number_of_acts - 1)) {
      col_indizes <- ((j - 1) * number_of_states + 1):(j * number_of_states)
      constr_mat[2 * j - 1, col_indizes] <- rbind(utility_table_woi[j, ] - utility_table_i)
      constr_mat[2 * j, col_indizes] <- rep(1, number_of_states)
    }
    constr_vec <- rep(c(0, 1), number_of_acts - 1)
    
    #compute a H-representation of all the constraints based on the probabilistic information
    hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
    
    # transforming the H-representation into a constraint-matrix, a constraint-vector and constraint directions for lpSolve
    for (j in 1:nrow(hrep)) {
      for (k in 1:(number_of_acts - 1)) {
        constr_mat <- rbind(constr_mat, rep(0, number_of_var))
        col_indizes <- ((k - 1) * number_of_states + 1):(k * number_of_states)
        constr_mat[nrow(constr_mat), col_indizes] <- hrep[j, -(1:2)] * (-1)
        constr_vec <- c(constr_vec, hrep[j, 2])
      }
    }
    constr_dir <- c(constr_dir, rep("<=", nrow(hrep) * (number_of_acts - 1)))
    
    # one optimizes over the sum of all optimization parameters or all probabilities for each comparison
    objective <- c(rep(1, number_of_states * (number_of_acts - 1)))
    
    # if optimal value is equal to the number of acts - 1, then act i can be considered as M-maximal
    # (rounding is required because there are small indifferences when optimizing)
    if (round(lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval, 10) == (number_of_acts - 1)) {
      m_maximal <- c(m_maximal, i)
    }
  }
  #E-admissible acts are also M-maximal
  m_maximal <- c(m_maximal, e_admissible_indices)
  output <- rbind(utility_table[m_maximal, ])
  row.names(output) <- row.names(utility_table)[m_maximal]
  return(output)
}

# function to compute the M-maximal acts
m_maximality <- function(panel, mode = c("utility","loss"), method = c("ep", "lp"), filter_admissible = TRUE, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  
  # check method to be a valid value
  method <- match.arg(method)
  
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # check if filter_admissible is a single logical value
  assert_flag(filter_admissible)
  
  #this will be used later
  number_of_states <- ncol(panel)
  
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # if there is only one row, the act is trivially M-maximal
  if (nrow(panel) == 1) {
    row.names(panel) <- 1:nrow(panel)
    return(panel)
  }
  
  # define the acts to be considered
  if (filter_admissible == TRUE) {
    admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
    utility_table <- rbind(panel[admissible_acts, ])
    row.names(utility_table) <- admissible_acts
  }
  else {
    utility_table <- panel
    row.names(utility_table) <- 1:nrow(panel)
  }
  
  if (method == "ep") { # method for m_maximality through applying strict dominance on the utility of acts VS extreme points
    return(m_maximality_ep(utility_table, mode, a1, b1, a2, b2, ordinal_structure, boundaries))
  }
  else if (method == "lp") { # method for m_maximality according to Jansen, 2018, computed by lpSolve
    return(m_maximality_lp(utility_table, mode, a1, b1, a2, b2, ordinal_structure, boundaries))
  }
}

# function to compute the E-admissible acts
e_admissibility <- function(panel, mode = c("utility","loss"), filter_strategy = c("admissible"), a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # filter_strategy must be an atomic vector 
  assert_atomic_vector(filter_strategy)
  
  # will be used later
  number_of_states <- ncol(panel)
  
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # different preprocessing and filtering of acts can have an impact on the computation speed
  if (prod(c("admissible", "m-maximal") %in% filter_strategy)) {
    utility_table <- m_maximality(panel, mode, "ep", TRUE, a1, b1, a2, b2, ordinal_structure, boundaries)
  }
  else if ("admissible" %in% filter_strategy) {
    admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
    utility_table <- panel[admissible_acts, ]
    row.names(utility_table) <- admissible_acts
  }
  else if ("m-maximal" %in% filter_strategy) {
    utility_table <- m_maximality(panel, mode, "ep", FALSE, a1, b1, a2, b2, ordinal_structure, boundaries)
  }
  else {
    utility_table <- panel
    row.names(utility_table) <- 1:nrow(panel)
  }
  
  # if there is only one row left, the act is trivially E-admissible
  if (nrow(utility_table) == 1) {
    return(utility_table)
  }
  
  e_admissible <- c()
  number_of_acts <- nrow(utility_table)
  number_of_states <- ncol(utility_table)
  
  for (i in 1:number_of_acts) {
    # constraints for the comparison between the current act to check for E-admissibility and all of the other acts
    #+ constraint for the sum of the states probabilities to have a maximum of 1
    if (mode == "utility") {
      constr_dir <- rep(c("<=", "<="), number_of_acts - 1)
    }
    else if (mode == "loss") {
      constr_dir <- rep(c(">=", "<="), number_of_acts - 1)
    }
    constr_mat <- matrix(0, (number_of_acts - 1) * 2, number_of_states)
    utility_table_woi <- rbind(utility_table[-i, ])
    utility_table_i <- rbind(utility_table[i, ])
    for (j in 1:(number_of_acts - 1)) {
      constr_mat[2 * j - 1, ] <- rbind(utility_table_woi[j, ] - utility_table_i)
      constr_mat[2 * j, ] <- rep(1, number_of_states)
    }
    constr_vec <- rep(c(0, 1), number_of_acts - 1)
    
    #compute a H-representation of all the constraints based on the probabilistic information
    hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
    
    # transforming the H-representation into a constraint-matrix, a constraint-vector and constraint directions for lpSolve
    for (j in 1:nrow(hrep)) {
      constr_mat <- rbind(constr_mat, rep(0, number_of_states))
      constr_mat[nrow(constr_mat), ] <- hrep[j, -(1:2)] * (-1)
      constr_vec <- c(constr_vec, hrep[j, 2])
    }
    constr_dir <- c(constr_dir, rep("<=", nrow(hrep)))
    
    # one optimizes over the sum of all optimization parameters or all probabilities
    objective <- c(rep(1, number_of_states))
    
    # if optimal value is equal to 1, then act i can be considered as E-admissible
    if (round(lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval, 10) == 1) {
      e_admissible <- c(e_admissible, i)
    }
  }
  output <- rbind(utility_table[e_admissible, ])
  row.names(output) <- row.names(utility_table)[e_admissible]
  return(output)
}

#function to compute the E-Epsilon-Admissible acts for a certain Epsilon
e_epsilon_admissibility <- function(panel, mode = c("utility","loss"), filter_strategy = c("admissible"), a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE), epsilon = 0) {
  
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # filter_strategy must be an atomic vector 
  assert_atomic_vector(filter_strategy)
  
  # check epsilon 
  check_normalized_parameter(epsilon)
  
  number_of_states <- ncol(panel)
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  #if epsilon = 0 or = 1 E-admissibility respectively M-maximality can be computed instead
  if (epsilon == 0) {
    return(e_admissibility(panel, mode, filter_strategy, a1, b1, a2, b2, ordinal_structure, boundaries))
  }
  else if (epsilon == 1) {
    return(m_maximality(panel, mode, "ep", TRUE, a1, b1, a2, b2, ordinal_structure, boundaries))
  }
  
  # Filtering can have a strong impact on the computation time
  e_admissible_indices <- c()
  if (prod(c("m-maximal", "e-admissible", "admissible") %in% filter_strategy)) {
    utility_table <- m_maximality(panel, mode, "ep", TRUE, a1, b1, a2, b2, ordinal_structure, boundaries)
    help_table <- utility_table
    row.names(help_table) <- 1:nrow(help_table)
    e_admissible_acts <- e_admissibility(help_table, mode, "none", a1, b1, a2, b2, ordinal_structure, boundaries)
    e_admissible_indices <- row.names(e_admissible_acts) %>% as.integer()
  }
  else if (prod(c("m-maximal", "e-admissible") %in% filter_strategy)) {
    utility_table <- m_maximality(panel, mode, "ep", FALSE, a1, b1, a2, b2, ordinal_structure, boundaries)
    help_table <- utility_table
    row.names(help_table) <- 1:nrow(help_table)
    e_admissible_acts <- e_admissibility(help_table, mode, "none", a1, b1, a2, b2, ordinal_structure, boundaries)
    e_admissible_indices <- row.names(e_admissible_acts) %>% as.integer()
  }
  else if (prod(c("m-maximal", "admissible") %in% filter_strategy)) {
    utility_table <- m_maximality(panel, mode, "ep", TRUE, a1, b1, a2, b2, ordinal_structure, boundaries)
  }
  else if ("m-maximal" %in% filter_strategy) {
    utility_table <- m_maximality(panel, mode, "ep", FALSE, a1, b1, a2, b2, ordinal_structure, boundaries)
  }
  else if (prod(c("e-admissible", "admissible") %in% filter_strategy)) {
    admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
    utility_table <- panel[admissible_acts, ]
    row.names(utility_table) <- admissible_acts
    help_table <- utility_table
    row.names(help_table) <- 1:nrow(help_table)
    e_admissible_acts <- e_admissibility(help_table, mode, "none", a1, b1, a2, b2, ordinal_structure, boundaries)
    e_admissible_indices <- row.names(e_admissible_acts) %>% as.integer()
  }
  else if ("e-admissible" %in% filter_strategy) {
    utility_table <- panel
    row.names(utility_table) <- 1:nrow(panel)
    e_admissible_acts <- e_admissibility(panel, mode, "none", a1, b1, a2, b2, ordinal_structure, boundaries)
    e_admissible_indices <- row.names(e_admissible_acts) %>% as.integer()
  }
  else if ("admissible" %in% filter_strategy) {
    admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
    utility_table <- panel[admissible_acts, ]
    row.names(utility_table) <- admissible_acts
  }
  else {
    utility_table <- panel
    row.names(utility_table) <- 1:nrow(panel)
  }
  
  # if there is only one row left, the act is trivially E-epsilon-admissible
  if (nrow(utility_table) == 1) {
    return(utility_table)
  }
  
  number_of_acts <- nrow(utility_table)
  number_of_states <- ncol(utility_table)
  
  e_epsilon_admissible <- c()
  for (i in setdiff(1:number_of_acts, e_admissible_indices)) {
    # constraints for the comparison between the current act to check for E-epsilon-admissibility and all of the other acts
    #+ constraint for the sum of the states probabilities to have a maximum of 1
    if (mode == "utility") {
      constr_dir <- rep(c("<=", "<="), number_of_acts - 1)
    }
    else if (mode == "loss") {
      constr_dir <- rep(c(">=", "<="), number_of_acts - 1)
    }
    constr_mat <- matrix(0, 2 * (number_of_acts - 1), (number_of_acts - 1) * number_of_states)
    number_of_var <- ncol(constr_mat)
    utility_table_woi <- rbind(utility_table[-i, ])
    utility_table_i <- rbind(utility_table[i, ])
    for (j in 1:(number_of_acts - 1)) {
      col_indizes <- ((j - 1) * number_of_states + 1):(j * number_of_states)
      constr_mat[2 * j - 1, col_indizes] <- rbind(utility_table_woi[j, ] - utility_table_i)
      constr_mat[2 * j, col_indizes] <- rep(1, number_of_states)
    }
    constr_vec <- rep(c(0, 1), number_of_acts - 1)
    
    #compute a H-representation of all the constraints based on the probabilistic information
    hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
    
    # transforming the H-representation into a constraint-matrix, a constraint-vector and constraint directions for lpSolve
    for (j in 1:nrow(hrep)) {
      for (k in 1:(number_of_acts - 1)) {
        constr_mat <- rbind(constr_mat, rep(0, number_of_var))
        col_indizes <- ((k - 1) * number_of_states + 1):(k * number_of_states)
        constr_mat[nrow(constr_mat), col_indizes] <- hrep[j, -(1:2)] * (-1)
        constr_vec <- c(constr_vec, hrep[j, 2])
      }
    }
    constr_dir <- c(constr_dir, rep("<=", nrow(hrep) * (number_of_acts - 1)))
    
    ## extra constraints for epsilon
    # use more optimization parameters to avoid absolute difference in constraint matrix
    constr_mat <- cbind(constr_mat, matrix(0, nrow = nrow(constr_mat), ncol = number_of_states * 2))
    number_of_var_new <- ncol(constr_mat)
    
    # each states probabilities for all comparisons of acts must be bounded,
    # by an upper boundary as well as an lower boundary...
    for (j in 1:number_of_states) {
      for (l in 1:(number_of_acts - 1)) {
        constr_mat <- rbind(constr_mat, rep(0, number_of_var_new))
        constr_mat[nrow(constr_mat), j + number_of_var] <- 1
        constr_mat[nrow(constr_mat), number_of_states * (l - 1) + j] <- -1
        constr_mat <- rbind(constr_mat, rep(0, number_of_var_new))
        constr_mat[nrow(constr_mat), j + number_of_states + number_of_var] <- -1
        constr_mat[nrow(constr_mat), number_of_states * (l - 1) + j] <- 1
      }
    }
    # the sum of every upper boundary - its corresponding lower boundary may not exceed epsilon
    constr_mat <- rbind(constr_mat, rep(0, number_of_var_new))
    constr_mat[nrow(constr_mat), (number_of_var + 1):(number_of_var + number_of_states)] <- -1
    constr_mat[nrow(constr_mat), (number_of_var + number_of_states + 1):number_of_var_new] <- 1
    
    new_constraint_rightside <- c(rep(0, 2 * (number_of_acts - 1) * number_of_states), epsilon)
    
    constr_vec <- c(constr_vec, new_constraint_rightside)
    constr_dir <- c(constr_dir, rep("<=", length(new_constraint_rightside)))
    
    # one optimizes over optimization parameters representing the states probabilities for each comparison
    objective <- c(rep(1, number_of_states * (number_of_acts - 1)), rep(0, number_of_states * 2))
    
    # if the optimal value of the problem equals the number of acts - 1 then act i is optimal in the sense of E-epsilon-admissibility
    # (rounding is required because there are small indifferences when optimizing)
    if (round(lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval, 10) == (number_of_acts - 1)) {
      e_epsilon_admissible <- c(e_epsilon_admissible, i)
    }
  }
  #E-admissible acts are also E-epsilon-admissible for every epsilon
  e_epsilon_admissible <- c(e_admissible_indices, e_epsilon_admissible)
  output <- rbind(utility_table[e_epsilon_admissible, ])
  row.names(output) <- row.names(utility_table)[e_epsilon_admissible]
  return(output)
}

#function to compute the E-Admissibility-Extent for some E-admissible acts 
e_admissibility_extent <- function(panel, mode = c("utility","loss"), measure = c("maximal","uniform"), e_admissible = NULL, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # measure must be one of 'maximal' , 'uniform'
  measure <- match.arg(measure)
  
  if (!is.null(e_admissible)) { 
    # if the e_admissible acts are given, check if they are valid acts
    assert_atomic_vector(e_admissible, min.len = 1, max.len = nrow(panel))
    assert_integerish(e_admissible, lower = 1, upper = nrow(panel))
  }
  
  number_of_states <- ncol(panel)
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # if the e_admissible acts are not given, compute them, otherwise trust the users input
  if (is.null(e_admissible)) {
    e_admissible_acts <- e_admissibility(panel, mode, c("admissible"), a1, b1, a2, b2, ordinal_structure, boundaries)
  }
  else {
    e_admissible_acts <- panel[e_admissible, ]
    row.names(e_admissible_acts) <- e_admissible
  }
  number_of_acts <- nrow(e_admissible_acts)
  number_of_states <- ncol(e_admissible_acts)
  
  extent <- data.frame(row.names = row.names(e_admissible_acts))
  extent$extent <- 0
  
  # If there is only one E-admissible act, its extent will always have its maximum (no computation required)
  if (nrow(e_admissible_acts) == 1) {
    stop("There is only one e-admissible action")
  }
  else if (measure == "maximal") {
    for (i in 1:number_of_acts) {
      # constraints to compare the utilities of the E-admissible acts
      if (mode == "utility") {
        constr_dir <- rep(c("<=", "=="), 2 * (number_of_acts - 1))
      }
      else if (mode == "loss") {
        constr_dir <- rep(c(">=", "=="), 2 * (number_of_acts - 1))
      }
      constr_mat <- matrix(0, 4 * (number_of_acts - 1), 2 * number_of_states)
      number_of_var <- ncol(constr_mat)
      e_admissible_acts_woi <- rbind(e_admissible_acts[-i, ])
      e_admissible_acts_i <- rbind(e_admissible_acts[i, ])
      for (j in 1:(number_of_acts - 1)) {
        for (k in 1:2) {
          col_indizes <- ((k - 1) * number_of_states + 1):(k * number_of_states)
          constr_mat[4 * (j - 1) + (k - 1) * 2 + 1, col_indizes] <- rbind(e_admissible_acts_woi[j, ] - e_admissible_acts_i)
          constr_mat[4 * (j - 1) + k * 2, col_indizes] <- rep(1, number_of_states)
        }
      }
      constr_vec <- rep(c(0, 1), 2 * (number_of_acts - 1))
      
      #compute a H-representation of all the constraints based on the probabilistic information
      hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
      
      # transforming the H-representation into a constraint-matrix, a constraint-vector and constraint directions for lpSolve
      for (j in 1:nrow(hrep)) {
        for (k in 1:2) {
          constr_mat <- rbind(constr_mat, rep(0, number_of_var))
          col_indizes <- ((k - 1) * number_of_states + 1):(k * number_of_states)
          constr_mat[nrow(constr_mat), col_indizes] <- hrep[j, -(1:2)] * (-1)
          constr_vec <- c(constr_vec, hrep[j, 2])
        }
      }
      constr_dir <- c(constr_dir, rep("<=", nrow(hrep) * 2))
      
      for (j in 1:number_of_states) {
        # for each state make an own optimization problem, to find the largest range of its possible probabilities over all possible distributions for which act i is the optimal act
        objective <- rep(0, number_of_states * 2)
        objective[j] <- 1
        objective[j + number_of_states] <- -1
        
        max_value_j <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval
        if (max_value_j > extent$extent[i]) {
          extent$extent[i] <- max_value_j
        }
      }
    }
  }
  else if (measure == "uniform") {
    for (i in 1:number_of_acts) {
      # constraints for states probabilities' sum to equal 1 and for each probability to be greater than epsilon
      constr_dir <- c("==", rep(">=", number_of_states))
      constr_vec <- c(1, rep(0, number_of_states))
      constr_mat <- matrix(c(rep(1, number_of_states), 0), 1, number_of_states + 1)
      constr_mat <- rbind(constr_mat, cbind(diag(1, number_of_states), rep(-1, number_of_states)))
      
      # constraints for comparing the E-admissible acts utilities (slightly adapted compared to maximal extent)
      if (mode == "utility") {
        constr_dir <- c(constr_dir, rep("<=", (number_of_acts - 1) * number_of_states * 2))
      }
      else if (mode == "loss") {
        constr_dir <- c(constr_dir, rep(">=", (number_of_acts - 1) * number_of_states * 2))
      }
      constr_vec <- c(constr_vec, rep(0, (number_of_acts - 1) * number_of_states * 2))
      e_admissible_acts_woi <- rbind(e_admissible_acts[-i, ])
      e_admissible_acts_i <- rbind(e_admissible_acts[i, ])
      for (j in 1:(number_of_acts - 1)) {
        difference_vector <- e_admissible_acts_woi[j, ] - e_admissible_acts_i
        for (k in 1:number_of_states) {
          constr_mat <- rbind(constr_mat, cbind(difference_vector, 0))
          constr_mat[nrow(constr_mat), ncol(constr_mat)] <- difference_vector[k] - mean(difference_vector[-k])
          constr_mat <- rbind(constr_mat, cbind(difference_vector, 0))
          constr_mat[nrow(constr_mat), ncol(constr_mat)] <- -difference_vector[k] + mean(difference_vector[-k])
        }
      }
      
      #compute a H-representation of all the constraints based on the probabilistic information
      hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
      
      # transforming the H-representation into a constraint-matrix, a constraint-vector and constraint directions for lpSolve
      for (j in 1:nrow(hrep)) {
        constraint_j <- hrep[j, -(1:2)] * (-1)
        for (k in 1:number_of_states) {
          constr_mat <- rbind(constr_mat, cbind(rbind(constraint_j), 0))
          constr_mat[nrow(constr_mat), ncol(constr_mat)] <- constraint_j[k] - mean(constraint_j[-k])
          constr_mat <- rbind(constr_mat, cbind(rbind(constraint_j), 0))
          constr_mat[nrow(constr_mat), ncol(constr_mat)] <- -constraint_j[k] + mean(constraint_j[-k])
          constr_vec <- c(constr_vec, rep(hrep[j, 2], 2))
        }
      }
      constr_dir <- c(constr_dir, rep("<=", nrow(hrep) * number_of_states * 2))
      row.names(constr_mat) <- 1:nrow(constr_mat)
      
      # The criterion can be solved with only one optimization problem per E-admissible act
      objective <- c(rep(0, number_of_states), 1)
      extent$extent[i] <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval
    }
  }
  return(extent)
}

# function to compute the optimal acts with respect to Gamma-Maximin
gamma_maximin <- function(panel, mode = c("utility","loss"), randomized_acts = TRUE, filter_admissible = TRUE, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # check if 'filter_admissible' and 'randomized_acts' are single logical values
  assert_flag(filter_admissible)
  assert_flag(randomized_acts)
  
  number_of_states <- ncol(panel)
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  number_of_acts <- nrow(panel)
  # if there is only one possible configuration of probabilities (only one extreme point), the criterion is equivalent to the Bayes-criterion
  if (sum(boundaries[, 2]) == 1) {
    expectations <- panel %*% boundaries[, 2]
    if (mode == "utility") {
      optimal <- max(expectations)
    }
    else if (mode == "loss") {
      optimal <- min(expectations)
    }
    optimal_acts <- (1:nrow(panel))[expectations == optimal]
    output <- data.frame(row.names = 1:length(optimal_acts))
    output$action <- optimal_acts
    output <- list(output, optimal)
    return(output)
  }
  
  probability_information <- !is.null(boundaries)
  
  # if randomized acts don't need to be considered and there is only trivial information on the states' probabilities, do the following:
  if (randomized_acts == FALSE && probability_information == FALSE) {
    criteria <- data.frame(row.names = 1:nrow(panel))
    criteria$value <- 0
    if (mode == "utility") {
      # simply look for the maximal minimum of the acts in the utility table
      for (i in 1:nrow(panel)) {
        criteria$value[i] <- min(panel[i, ])
      }
      maximum <- max(criteria)
      optimal <- (1:nrow(criteria))[criteria == maximum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, maximum)
      return(output)
    }
    else if (mode == "loss") {
      # instead look for the minimla maximum of the acts...
      for (i in 1:nrow(panel)) {
        criteria$value[i] <- max(panel[i, ])
      }
      minimum <- min(criteria)
      optimal <- (1:nrow(criteria))[criteria == minimum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, minimum)
      return(output)
    }
  }
  else if (probability_information == TRUE && randomized_acts == FALSE) { 
    # if there are non-trivial requirements on the states' probabilities and randomized acts shall not be considered:
    if (filter_admissible == TRUE) {
      admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
      utility_table <- rbind(panel[admissible_acts, ])
      row.names(utility_table) <- admissible_acts
    }
    else {
      utility_table <- panel
      row.names(utility_table) <- 1:nrow(panel)
    }
    criteria <- data.frame(row.names = 1:nrow(utility_table))
    criteria$action <- row.names(utility_table)
    criteria$value <- 0
    
    number_of_acts <- nrow(utility_table)
    number_of_states <- ncol(utility_table)
    
    # states' probabilities sum must equal 1
    constr_mat <- matrix(rep(1, number_of_states), nrow = 1, ncol = number_of_states)
    constr_vec <- c(1)
    constr_dir <- c("==")
    
    #compute a H-representation of all the constraints based on the probabilistic information
    hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
    
    for (j in 1:nrow(hrep)) {
      constr_mat <- rbind(constr_mat, rep(0, number_of_states))
      constr_mat[nrow(constr_mat), ] <- hrep[j, -(1:2)] * (-1)
      constr_vec <- c(constr_vec, hrep[j, 2])
    }
    constr_dir <- c(constr_dir, rep("<=", nrow(hrep)))
    
    for (i in 1:nrow(criteria)) {
      objective <- utility_table[i, ]
      worst_case <- 0
      best_case <- 0
      
      if (mode == "utility") {
        # for each act minimize the utility expectation function to get the Gamma-Maxi-Min criterion
        criteria$value[i] <- lp(direction = "min", objective, constr_mat, constr_dir, constr_vec)$objval
      }
      else if (mode == "loss") {
        # maximize instead for the Gamma-Mini-Max criterion
        criteria$value[i] <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval
      }
    }
    if (mode == "utility") {
      # The maximum of all acts' minimum values defines the optimal act
      maximum <- max(criteria$value)
      optimal <- criteria$action[criteria$value == maximum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, maximum)
      return(output)
    }
    else if (mode == "loss") {
      # The minimum of all acts' maximum values defines the optimal act
      minimum <- min(criteria$value)
      optimal <- criteria$action[criteria$value == minimum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, minimum)
      return(output)
    }
  }
  else if (randomized_acts == TRUE && probability_information == FALSE) { 
    # if randomized acts are considered but there are no non-trivial probability requirements:
    if (filter_admissible == TRUE) {
      admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
      utility_table <- rbind(panel[admissible_acts, ])
      row.names(utility_table) <- admissible_acts
    }
    else {
      utility_table <- panel
      row.names(utility_table) <- 1:nrow(panel)
    }
    number_of_acts <- nrow(utility_table)
    number_of_states <- ncol(utility_table)
    
    # states probabilities' sum must equal 1
    constr_mat <- matrix(c(0, 0, rep(1, number_of_acts)), nrow = 1, ncol = number_of_acts + 2)
    constr_vec <- c(1)
    constr_dir <- c("==")
    
    # each state must have a probability of at least 0
    constr_mat <- rbind(constr_mat, diag(1, ncol(constr_mat)))
    constr_vec <- c(constr_vec, rep(0, ncol(constr_mat)))
    constr_dir <- c(constr_dir, rep(">=", ncol(constr_mat)))
    
    if (mode == "utility") {
      # the lower limit of utility among all states needs to be maximized
      constr_mat <- constr_mat
      for (j in 1:number_of_states) {
        constr_mat <- rbind(constr_mat, c(1, -1, (-1) * utility_table[, j]))
      }
      constr_vec <- c(constr_vec, rep(0, number_of_states))
      constr_dir <- c(constr_dir, rep("<=", number_of_states))
      objective <- c(1, -1, rep(0, number_of_acts))
      
      optimization <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)
    }
    else if (mode == "loss") {
      # respectively the upper limit of loss among all states needs to be minimized
      constr_mat <- constr_mat
      for (j in 1:number_of_states) {
        constr_mat <- rbind(constr_mat, c(1, -1, (-1) * utility_table[, j]))
      }
      constr_vec <- c(constr_vec, rep(0, number_of_states))
      constr_dir <- c(constr_dir, rep(">=", number_of_states))
      objective <- c(1, -1, rep(0, number_of_acts))
      
      optimization <- lp(direction = "min", objective, constr_mat, constr_dir, constr_vec)
    }
    output <- data.frame(row.names = 1:nrow(utility_table))
    output$action <- row.names(utility_table)
    output$weight <- optimization$solution[-c(1, 2)]
    output <- list(output, optimization$objval)
    return(output)
  }
  else if (randomized_acts == TRUE && probability_information == TRUE) { 
    # if there is consideration of randomized acts as well as non-trivial information on the states' probabilities
    if (filter_admissible == TRUE) {
      admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
      utility_table <- rbind(panel[admissible_acts, ])
      row.names(utility_table) <- admissible_acts
    }
    else {
      utility_table <- panel
      row.names(utility_table) <- 1:nrow(panel)
    }
    criteria <- data.frame(row.names = 1:nrow(utility_table))
    criteria$action <- row.names(utility_table)
    criteria$value <- 0
    
    number_of_acts <- nrow(utility_table)
    number_of_states <- ncol(utility_table)
    
    #compute a H-representation of all the constraints based on the probabilistic information
    hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
    
    # This is solved via a dual programming problem where there are two optimization variables for each constraint of the H-representation of the probability requirements, one parameter per act plus two additional slack variables
    number_of_var <- 2 + nrow(hrep) * 2 + number_of_acts
    
    # The weights of the acts must equal 1
    constr_mat <- matrix(c(rep(0, number_of_var - number_of_acts), rep(1, number_of_acts)), nrow = 1, ncol = number_of_var)
    constr_vec <- c(1)
    constr_dir <- c("==")
    
    # Every optimization variables must be >= 0
    constr_mat <- rbind(constr_mat, diag(1, number_of_var))
    constr_vec <- c(constr_vec, rep(0, number_of_var))
    constr_dir <- c(constr_dir, rep(">=", number_of_var))
    
    objective <- c(1, -1, rep(0, number_of_var - 2))
    
    # add a constraint for each constraint in the H-representation of the probability requirements and remember all of the rows
    checkpoint1 <- nrow(constr_mat) + 1
    for (j in 1:number_of_states) {
      constr_mat <- rbind(constr_mat, c(1, -1, rep(0, nrow(hrep) * 2), (-1) * utility_table[, j]))
    }
    checkpoint2 <- nrow(constr_mat)
    constraints_to_alter <- checkpoint1:checkpoint2
    
    constr_vec <- c(constr_vec, rep(0, number_of_states))
    if (mode == "utility") {
      constr_dir <- c(constr_dir, rep("<=", number_of_states))
      for (j in 1:nrow(hrep)) {
        # for every line of the H-representation add the respective boundary as factor to the objective vector
        # additionally add the parameters of states in the H-representation in their respective column of the constraint matrix
        objective_value <- hrep[j, 2] * (-1)
        if (objective_value >= 0) {
          objective[2 + j] <- objective_value
          constr_mat[constraints_to_alter, 2 + j] <- (hrep[j, -(1:2)])
        }
        else if (objective_value < 0) {
          objective[2 + nrow(hrep) + j] <- objective_value
          constr_mat[constraints_to_alter, 2 + nrow(hrep) + j] <- (hrep[j, -(1:2)])
        }
      }
    }
    else if (mode == "loss") {
      # for loss the the signs and positions of the optimization variables must be switched
      constr_dir <- c(constr_dir, rep(">=", number_of_states))
      for (j in 1:nrow(hrep)) {
        objective_value <- hrep[j, 2]
        if (objective_value <= 0) {
          objective[2 + j] <- objective_value
          constr_mat[constraints_to_alter, 2 + j] <- (-1) * (hrep[j, -(1:2)])
        }
        else if (objective_value > 0) {
          objective[2 + nrow(hrep) + j] <- objective_value
          constr_mat[constraints_to_alter, 2 + nrow(hrep) + j] <- (-1) * (hrep[j, -(1:2)])
        }
      }
    }
    
    # zero-rows of the constraint matrix can be excluded
    i <- 1
    while (i <= nrow(constr_mat)) {
      if (prod(constr_mat[i, ] == 0) == 1) {
        constr_mat <- constr_mat[-i, ]
        constr_vec <- constr_vec[-i]
        constr_dir <- constr_dir[-i]
        i <- i - 1
      }
      i <- i + 1
    }
    
    # maximize for utility and minimize for loss
    if (mode == "utility") {
      optimization <- lp("max", objective, constr_mat, constr_dir, constr_vec)
    }
    else if (mode == "loss") {
      optimization <- lp("min", objective, constr_mat, constr_dir, constr_vec)
    }
    
    output <- data.frame(row.names = 1:number_of_acts)
    output$action <- row.names(utility_table)
    output$weight <- tail(optimization$solution, number_of_acts)
    output <- list(output, optimization$objval)
    return(output)
  }
}

# function to compute the optimal Hodges-Lehmann-criterion acts
hodges_lehmann <- function(panel, mode = c("utility","loss"), priori = NULL, trust = 0, randomized_acts = TRUE, filter_admissible = TRUE) {
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  #requirements concerning the priori distribution
  if (!is.null(priori)) {
    check_priori_requirements(panel,priori)
  }
  else {
    #if no priori is given, trust will automatically be set to 0
    trust <- 0
  }
  
  # check if trust is a valid parameter
  check_normalized_parameter(trust)
  
  # check if 'filter_admissible' and 'randomized_acts' are single logical values
  assert_flag(filter_admissible)
  assert_flag(randomized_acts)
  
  # if trust is equal to 0, this criterion is equivalent to the Gamma-Maxi-Min criterion with trivial extreme points (= Maxi-Min criterion)
  if (trust == 0) {
    return(gamma_maximin(panel, mode, randomized_acts, filter_admissible))
  }
  else if (randomized_acts == FALSE || trust == 1) {
    # The criterion value for pure acts is simply a linear combination of the Bayes-criterion and the Maxi-Min criterion
    expectations <- panel %*% priori
    criteria <- expectations * trust
    if (mode == "utility") {
      if (trust < 1) {
        for (i in 1:nrow(panel)) {
          criteria[i, ] <- criteria[i, ] + (1 - trust) * min(panel[i, ])
        }
      }
      maximum <- max(criteria)
      optimal <- (1:nrow(criteria))[criteria == maximum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, maximum)
      return(output)
    }
    else if (mode == "loss") {
      if (trust < 1) {
        for (i in 1:nrow(panel)) {
          criteria[i, ] <- criteria[i, ] + (1 - trust) * max(panel[i, ])
        }
      }
      minimum <- min(criteria)
      optimal <- (1:nrow(criteria))[criteria == minimum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, minimum)
      return(output)
    }
  }
  else if (randomized_acts == TRUE) { 
    # if randomized acts are considered one can generate the optimal criterion by solving the following lp problem
    if (filter_admissible == TRUE) {
      admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
      utility_table <- rbind(panel[admissible_acts, ])
      row.names(utility_table) <- admissible_acts
    }
    else {
      utility_table <- panel
      row.names(utility_table) <- 1:nrow(panel)
    }
    
    number_of_acts <- nrow(utility_table)
    number_of_states <- ncol(utility_table)
    
    # compute utility expectation
    expectations <- utility_table %*% priori
    # the sum of the act weights for a randomized act must equal 1
    constr_mat <- matrix(c(rep(0, 2), rep(1, number_of_acts)), nrow = 1, ncol = number_of_acts + 2)
    constr_vec <- c(1)
    constr_dir <- c("==")
    
    # probabilities must be >= 0
    constr_mat <- rbind(constr_mat, diag(1, ncol(constr_mat)))
    constr_vec <- c(constr_vec, rep(0, ncol(constr_mat)))
    constr_dir <- c(constr_dir, rep(">=", ncol(constr_mat)))
    
    # two constraints represent the randomized acts worst case
    for (i in 1:number_of_states) {
      constr_mat <- rbind(constr_mat, c(1, -1, (-1) * utility_table[, i]))
    }
    constr_vec <- c(constr_vec, rep(0, number_of_states))
    
    if (mode == "utility") {
      constr_dir <- c(constr_dir, rep("<=", number_of_states))
    }
    else if (mode == "loss") {
      constr_dir <- c(constr_dir, rep(">=", number_of_states))
    }
    
    # this represents the criteria value
    # note that the worst case is split upon the first two optimization parameters
    objective <- c(1 - trust, trust - 1, trust * expectations)
    
    if (mode == "utility") {
      optimization <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)
    }
    else if (mode == "loss") {
      optimization <- lp(direction = "min", objective, constr_mat, constr_dir, constr_vec)
    }
    output <- data.frame(row.names = 1:nrow(utility_table))
    output$action <- row.names(utility_table)
    # the solution of the optimization problem represents the optimal randomized act
    output$weight <- optimization$solution[-c(1, 2)]
    output <- list(output, optimization$objval)
    return(output)
  }
}

# function to compute the Hurwicz-optimal act
hurwicz <- function(panel, mode = c("utility","loss"), optimism = 0, randomized_acts = TRUE, filter_admissible = TRUE, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # check if optimism is a valid parameter
  check_normalized_parameter(optimism)
  
  # check if 'filter_admissible' and 'randomized_acts' are single logical values
  assert_flag(filter_admissible)
  assert_flag(randomized_acts)
  
  number_of_states <- ncol(panel)
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # if boundaries is NULL there is no probabilistic information
  probability_information <- !is.null(boundaries)
  
  # if no randomized acts are considered and there is only trivial information about the states distribution the computation is a lot easier
  if (randomized_acts == FALSE && probability_information == FALSE) {
    criteria <- data.frame(row.names = 1:nrow(panel))
    criteria$value <- 0
    if (mode == "utility") {
      if (optimism < 1 && optimism > 0) {
        # for the case of 0 < optimism < 1, the criteria score of each act is simply a linear combination of its maximum and minimum utility value
        for (i in 1:nrow(panel)) {
          criteria$value[i] <- max(panel[i, ]) * optimism + min(panel[i, ]) * (1 - optimism)
        }
      }
      else if (optimism == 1) {
        # for the case of optimism = 1, the criteria score of each act is simply its maximum utility value
        for (i in 1:nrow(panel)) {
          criteria$value[i] <- max(panel[i, ])
        }
      }
      else if (optimism == 0) {
        # for the case of optimism = 0, the criteria score of each act is simply its minimum utility value
        for (i in 1:nrow(panel)) {
          criteria$value[i] <- min(panel[i, ])
        }
      }
      maximum <- max(criteria)
      optimal <- (1:nrow(criteria))[criteria == maximum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, maximum)
      return(output)
    }
    else if (mode == "loss") {
      # in case of loss the criteria value is computed in the opposite way as for utility
      if (optimism < 1 && optimism > 0) {
        for (i in 1:nrow(panel)) {
          criteria$value[i] <- min(panel[i, ]) * optimism + max(panel[i, ]) * (1 - optimism)
        }
      }
      else if (optimism == 1) {
        for (i in 1:nrow(panel)) {
          criteria$value[i] <- min(panel[i, ])
        }
      }
      else if (optimism == 0) {
        for (i in 1:nrow(panel)) {
          criteria$value[i] <- max(panel[i, ])
        }
      }
      minimum <- min(criteria)
      optimal <- (1:nrow(criteria))[criteria == minimum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, minimum)
      return(output)
    }
  }
  else if (probability_information == TRUE && randomized_acts == FALSE) {
    # when there is non-trivial information on the state distribution but randomized acts are not considered do the following:
    
    # filtering for admissibility can have an impact on the running time
    if (filter_admissible == TRUE) {
      admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
      utility_table <- rbind(panel[admissible_acts, ])
      row.names(utility_table) <- admissible_acts
    }
    else {
      utility_table <- panel
      row.names(utility_table) <- 1:nrow(panel)
    }
    criteria <- data.frame(row.names = 1:nrow(utility_table))
    criteria$action <- row.names(utility_table)
    criteria$value <- 0
    
    number_of_acts <- nrow(utility_table)
    number_of_states <- ncol(utility_table)
    
    # the states probabilities sum must equal 1
    constr_mat <- matrix(rep(1, number_of_states), nrow = 1, ncol = number_of_states)
    constr_vec <- c(1)
    constr_dir <- c("==")
    
    # compute a H-representation of all the constraints based on the probabilistic information
    hrep <- generate_probability_constraints(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
    
    # transforming the H-representation into a constraint-matrix, a constraint-vector and constraint directions for lpSolve
    for (j in 1:nrow(hrep)) {
      constr_mat <- rbind(constr_mat, rep(0, number_of_states))
      constr_mat[nrow(constr_mat), ] <- hrep[j, -(1:2)] * (-1)
      constr_vec <- c(constr_vec, hrep[j, 2])
    }
    constr_dir <- c(constr_dir, rep("<=", nrow(hrep)))
    
    for (i in 1:nrow(criteria)) {
      # compute the criteria value for each act with a linear programming problem
      objective <- utility_table[i, ]
      worst_case <- 0
      best_case <- 0
      
      if (mode == "utility") {
        if (optimism < 1) {
          # the worst case is only required if optimism is < 1
          worst_case <- lp(direction = "min", objective, constr_mat, constr_dir, constr_vec)$objval
        }
        if (optimism > 0) {
          # the best case is only required if optimism is > 0
          best_case <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval
        }
        # the criteria value is a linear combination of worst and best case
        criteria$value[i] <- worst_case * (1 - optimism) + best_case * optimism
      }
      else if (mode == "loss") {
        # linear programming problems are switched for loss compared to utility
        if (optimism < 1) {
          worst_case <- lp(direction = "max", objective, constr_mat, constr_dir, constr_vec)$objval
        }
        if (optimism > 0) {
          best_case <- lp(direction = "min", objective, constr_mat, constr_dir, constr_vec)$objval
        }
        criteria$value[i] <- worst_case * (1 - optimism) + best_case * optimism
      }
    }
    if (mode == "utility") {
      # the act(s) with maximal criteria value is/are optimal
      maximum <- max(criteria$value)
      optimal <- criteria$action[criteria$value == maximum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, maximum)
      return(output)
    }
    else if (mode == "loss") {
      # the act(s) with minimal criteria value is/are optimal
      minimum <- min(criteria$value)
      optimal <- criteria$action[criteria$value == minimum]
      output <- data.frame(row.names = 1:length(optimal))
      output$action <- optimal
      output <- list(output, minimum)
      return(output)
    }
  }
  else if (randomized_acts == TRUE) {
    # if randomized acts have to be considered do the following:
    if (optimism == 0) {
      # if optimism equals 0, then use the Gamma-Maxi-Min function instead
      return(gamma_maximin(panel, mode, randomized_acts, filter_admissible, a1, b1, a2, b2, ordinal_structure, boundaries))
    }
    if (optimism == 1) {
      # Gamma-Maxi-Max is a special case because it cannot be computed the same way as Gamma-Maxi-Min because the linear programming problem would be unbounded
      if (filter_admissible == TRUE) {
        admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
        utility_table <- rbind(panel[admissible_acts, ])
        row.names(utility_table) <- admissible_acts
      }
      else {
        utility_table <- panel
        row.names(utility_table) <- 1:nrow(panel)
      }
      
      number_of_acts <- nrow(utility_table)
      number_of_states <- ncol(utility_table)
      
      # computing the extreme points for the states' probabilities
      if (is.null(boundaries)) {
        extreme_points <- diag(1, number_of_states)
      }
      else {
        extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
      }
      
      # consider the utility values of the acts for the extreme points
      extreme_point_utility <- utility_table %*% t(extreme_points)
      
      if (mode == "utility") {
        is_max_extreme_points <- extreme_point_utility == max(extreme_point_utility)
        number_of_extreme_points <- nrow(extreme_points)
        
        best_case_acts <- list()
        best_case_acts_length <- list()
        new_length <- 1
        
        for (j in 1:number_of_extreme_points) {
          if (sum(is_max_extreme_points[, j]) > 0) {
            # only consider states which have maximum possible utility for at least one act
            # all of these acts' linear combinations are optimal acts in concern to Gamma - Maxi-Max
            best_case_acts[[new_length]] <- as.integer((row.names(utility_table))[is_max_extreme_points[, j]])
            best_case_acts_length[[new_length]] <- length(best_case_acts[[new_length]])
            new_length <- new_length + 1
          }
        }
        
        # the following part of the code excludes redundant combinations f.e. (A1,A2) will be excluded, if (A1,A2,A3) is also optimal
        output <- list()
        best_case_acts_length <- unlist(best_case_acts_length)
        best_case_acts_order <- order(best_case_acts_length, decreasing = TRUE)
        best_case_acts_exclude <- c()
        
        i <- 1
        while (i < new_length - 1) {
          j <- i + 1
          while (j <= new_length - 1) {
            if (prod(best_case_acts[[best_case_acts_order[j]]] %in% best_case_acts[[best_case_acts_order[i]]]) == 1) {
              best_case_acts_exclude <- c(best_case_acts_exclude, j)
            }
            j <- j + 1
          }
          i <- i + 1
        }
        
        best_case_acts_exclude <- best_case_acts_order[unique(best_case_acts_exclude)]
        if (length(best_case_acts_exclude) != 0) {
          best_case_acts <- best_case_acts[-best_case_acts_exclude]
        }
        
        output[[1]] <- best_case_acts
        output[[2]] <- max(extreme_point_utility)
        return(output)
      }
      else if (mode == "loss") {
        # instead of considering the maximum utility, consider the minimal loss
        is_min_extreme_points <- extreme_point_utility == min(extreme_point_utility)
        number_of_extreme_points <- nrow(extreme_points)
        
        best_case_acts <- list()
        best_case_acts_length <- list()
        new_length <- 1
        
        for (j in 1:number_of_extreme_points) {
          if (sum(is_min_extreme_points[, j]) > 0) {
            best_case_acts[[new_length]] <- as.integer((row.names(utility_table))[is_min_extreme_points[, j]])
            best_case_acts_length[[new_length]] <- length(best_case_acts[[new_length]])
            new_length <- new_length + 1
          }
        }
        
        output <- list()
        best_case_acts_length <- unlist(best_case_acts_length)
        best_case_acts_order <- order(best_case_acts_length, decreasing = TRUE)
        best_case_acts_exclude <- c()
        
        i <- 1
        while (i < new_length - 1) {
          j <- i + 1
          while (j <= new_length - 1) {
            if (prod(best_case_acts[[best_case_acts_order[j]]] %in% best_case_acts[[best_case_acts_order[i]]]) == 1) {
              best_case_acts_exclude <- c(best_case_acts_exclude, j)
            }
            j <- j + 1
          }
          i <- i + 1
        }
        
        best_case_acts_exclude <- best_case_acts_order[unique(best_case_acts_exclude)]
        if (length(best_case_acts_exclude) != 0) {
          best_case_acts <- best_case_acts[-best_case_acts_exclude]
        }
        
        output[[1]] <- best_case_acts
        output[[2]] <- min(extreme_point_utility)
        return(output)
      }
    }
    else {
      # if 0 < optimism< 1 do the following:
      if (filter_admissible == TRUE) {
        admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
        utility_table <- rbind(panel[admissible_acts, ])
        row.names(utility_table) <- admissible_acts
      }
      else {
        utility_table <- panel
        row.names(utility_table) <- 1:nrow(panel)
      }
      
      number_of_acts <- nrow(utility_table)
      number_of_states <- ncol(utility_table)
      
      # constraint for states probabilities' sum to equal 1
      constr_mat <- matrix(c(0, 0, rep(1, number_of_acts)), nrow = 1, ncol = number_of_acts + 2)
      constr_vec <- c(1)
      constr_dir <- c("==")
      
      # constraint for each states' probability to be strictly greater
      constr_mat <- rbind(constr_mat, diag(1, ncol(constr_mat)))
      constr_vec <- c(constr_vec, rep(0, ncol(constr_mat)))
      constr_dir <- c(constr_dir, rep(">=", ncol(constr_mat)))
      
      # define the set of extreme points
      if (is.null(boundaries)) {
        extreme_points <- diag(1, number_of_states)
      }
      else {
        extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
      }
      
      # compute the utility of each act for each extreme point
      extreme_point_utility <- utility_table %*% t(extreme_points)
      number_of_extreme_points <- nrow(extreme_points)
      
      # add constraint for utilities of each state
      for (j in 1:number_of_extreme_points) {
        constr_mat <- rbind(constr_mat, c(1, -1, (-1) * extreme_point_utility[, j]))
      }
      constr_vec <- c(constr_vec, rep(0, number_of_extreme_points))
      
      if (mode == "utility") {
        constr_dir <- c(constr_dir, rep("<=", number_of_extreme_points))
        weights <- NA
        current_best <- -Inf
        
        # for each extreme point solve a separate linear programming problem to find the optimal randomized act and its criteria value
        # the opitimal solution among all solutions is the randomized optimal act
        for (j in 1:number_of_extreme_points) {
          objective <- c(1 - optimism, optimism - 1, optimism * extreme_point_utility[, j])
          optimization <- lp("max", objective, constr_mat, constr_dir, constr_vec)
          if (optimization$objval > current_best) {
            current_best <- optimization$objval
            weights <- optimization$solution
          }
        }
      }
      else if (mode == "loss") {
        # for loss change direction of constraint (worst case is maximum instead of minimum)
        constr_dir <- c(constr_dir, rep(">=", number_of_extreme_points))
        weights <- NA
        current_best <- Inf
        
        for (j in 1:number_of_extreme_points) {
          objective <- c(1 - optimism, optimism - 1, optimism * extreme_point_utility[, j])
          # minimize instead of maximize
          optimization <- lp("min", objective, constr_mat, constr_dir, constr_vec)
          if (optimization$objval < current_best) {
            current_best <- optimization$objval
            weights <- optimization$solution
          }
        }
      }
      output <- data.frame(row.names = 1:nrow(utility_table))
      output$action <- row.names(utility_table)
      # the optimal randomized act is induced by the solution of the optimization problem
      output$weight <- weights[-c(1, 2)]
      output <- list(output, current_best)
      return(output)
    }
  }
}

# function to compute the optimal act with respect to Stochastic Dominance
stochastic_dominance <- function(panel, mode = c("utility","loss"), mode2 = c("joint","pairwise"), priori = NULL, filter_admissible = TRUE, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # mode2 must be one of 'joint', 'pairwise'
  mode2 <- match.arg(mode2)
  
  # check if 'filter_admissible' is a single logical value
  assert_flag(filter_admissible)
  
  # requirements concerning the optional priori distribution
  if (!is.null(priori)) {
    check_priori_requirements(panel,priori)
  }
  
  number_of_states <- ncol(panel)
  
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # if no priori is given, use the extreme points from the probability requirements instead
  if (is.null(priori)) {
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    if (nrow(extreme_points) == 1) {
      priori <- extreme_points
    }
  }
  
  if (filter_admissible == TRUE) {
    admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
    utility_table <- rbind(panel[admissible_acts, ])
    row.names(utility_table) <- admissible_acts
  }
  else {
    utility_table <- panel
    row.names(utility_table) <- 1:nrow(panel)
  }
  
  # if there is only one act to be considered, it is also optimal with respect to stochastic dominance
  number_of_acts <- nrow(utility_table)
  if (number_of_acts == 1) {
    return(utility_table)
  }
  
  if (mode2 == "joint") {
    # There is one optimization variable for each combination of act and state + additional epsilon variable
    ## all of these variables (except epsilon) must be <= 1
    ## all of these variables (including epsilon) must be >= 0
    number_of_var <- number_of_states * number_of_acts + 1
    constr_mat <- diag(1, number_of_var)
    constr_mat <- constr_mat[-1, ]
    constr_vec <- rep(1, number_of_var - 1)
    constr_dir <- rep("<=", number_of_var - 1)
    
    constr_mat <- rbind(constr_mat, diag(1, number_of_var))
    constr_vec <- c(constr_vec, rep(0, number_of_var))
    constr_dir <- c(constr_dir, rep(">=", number_of_var))
    
    # compare each pair of utility table entries
    for (i in 1:number_of_acts) {
      for (j in 1:number_of_states) {
        for (k in i:number_of_acts) {
          compare_same <- i == k
          if (compare_same && j == number_of_states) {
            next
          }
          for (l in (compare_same * j + 1):number_of_states) {
            if (i != k || j != l) {
              # if one entry is strictly greater than the other add a constraint for the respective optimization variables to represent that inequality with a difference of at least epsilon
              if (utility_table[i, j] > utility_table[k, l]) {
                constr_mat <- rbind(constr_mat, rep(0, number_of_var))
                constr_mat[nrow(constr_mat), 1 + (i - 1) * number_of_states + j] <- -1
                constr_mat[nrow(constr_mat), 1 + (k - 1) * number_of_states + l] <- 1
                constr_mat[nrow(constr_mat), 1] <- 1
                constr_dir <- c(constr_dir, "<=")
                constr_vec <- c(constr_vec, 0)
              }
              else if (utility_table[i, j] < utility_table[k, l]) {
                constr_mat <- rbind(constr_mat, rep(0, number_of_var))
                constr_mat[nrow(constr_mat), 1 + (i - 1) * number_of_states + j] <- 1
                constr_mat[nrow(constr_mat), 1 + (k - 1) * number_of_states + l] <- -1
                constr_mat[nrow(constr_mat), 1] <- 1
                constr_dir <- c(constr_dir, "<=")
                constr_vec <- c(constr_vec, 0)
              }
              else { 
                # if both entries are equivalent then include a constraint which sets the respective optimization variables as equal too
                constr_mat <- rbind(constr_mat, rep(0, number_of_var))
                constr_mat[nrow(constr_mat), 1 + (i - 1) * number_of_states + j] <- 1
                constr_mat[nrow(constr_mat), 1 + (k - 1) * number_of_states + l] <- -1
                constr_dir <- c(constr_dir, "==")
                constr_vec <- c(constr_vec, 0)
              }
            }
          }
        }
      }
    }
    
    # extend the constraint vector and the respective directions by the number of extreme points (= 1 if there is a priori)
    if (is.null(priori)) {
      constr_vec <- c(constr_vec, rep(0, (number_of_acts - 1) * nrow(extreme_points)))
      
      if (mode == "utility") {
        constr_dir <- c(constr_dir, rep(">=", (number_of_acts - 1) * nrow(extreme_points)))
      }
      else if (mode == "loss") {
        constr_dir <- c(constr_dir, rep("<=", (number_of_acts - 1) * nrow(extreme_points)))
      }
    }
    else {
      constr_vec <- c(constr_vec, rep(0, (number_of_acts - 1)))
      
      if (mode == "utility") {
        constr_dir <- c(constr_dir, rep(">=", (number_of_acts - 1)))
      }
      else if (mode == "loss") {
        constr_dir <- c(constr_dir, rep("<=", (number_of_acts - 1)))
      }
    }
    
    # epsilon shall be maximized
    objective <- c(1, rep(0, number_of_var - 1))
    
    # this refers to the algorithm in Jansen, 2018, p. 83
    # the optimization parameters work as substitution for the 'actual utility' 
    # one compares the acts expectations for different kind of utilities fulfilling the same ordinal relations
    stochastic_dominance_optimal <- c()
    for (i in 1:number_of_acts) {
      constr_mat_i <- rbind(constr_mat, rep(0, number_of_var))
      current_row <- nrow(constr_mat_i)
      constr_mat_i[current_row, (2 + (i - 1) * number_of_states):(1 + i * number_of_states)] <- rep(1, number_of_states)
      for (i2 in 1:number_of_acts) {
        if (i2 != i) {
          constr_mat_i <- rbind(constr_mat_i, constr_mat_i[current_row, ])
          constr_mat_i[nrow(constr_mat_i), (2 + (i2 - 1) * number_of_states):(1 + i2 * number_of_states)] <- rep(-1, number_of_states)
          current_row2 <- nrow(constr_mat_i)
          if (is.null(priori)) {
            for (j in 1:nrow(extreme_points)) {
              constr_mat_i <- rbind(constr_mat_i, constr_mat_i[current_row2, ])
              constr_mat_i[nrow(constr_mat_i), (2:ncol(constr_mat_i))] <- rep(extreme_points[j, ], number_of_acts) * constr_mat_i[nrow(constr_mat_i), (2:ncol(constr_mat_i))]
            }
          }
          else {
            constr_mat_i <- rbind(constr_mat_i, constr_mat_i[current_row2, ])
            constr_mat_i[nrow(constr_mat_i), (2:ncol(constr_mat_i))] <- priori * constr_mat_i[nrow(constr_mat_i), (2:ncol(constr_mat_i))]
          }
          constr_mat_i <- constr_mat_i[-current_row2, ]
        }
      }
      constr_mat_i <- constr_mat_i[-current_row, ]
      
      optimization <- lp("max", objective, constr_mat_i, constr_dir, constr_vec)
      
      if (optimization$objval > 0) {
        stochastic_dominance_optimal <- c(stochastic_dominance_optimal, i)
      }
    }
    output <- rbind(utility_table[stochastic_dominance_optimal, ])
    row.names(output) <- row.names(utility_table)[stochastic_dominance_optimal]
    return(output)
  }
  else if (mode2 == "pairwise") {
    # the pairwise algorithm is basically the same as for the joint version.
    # Instead of comparing act i to all other acts at the same time, one just compares it successively to all of the other acts.
    number_of_var <- number_of_states * 2 + 1
    objective <- c(1, rep(0, number_of_var - 1))
    constr_mat <- diag(1, number_of_var)
    constr_mat <- constr_mat[-1, ]
    constr_vec <- rep(1, number_of_var - 1)
    constr_dir <- rep("<=", number_of_var - 1)
    
    constr_mat <- rbind(constr_mat, diag(1, number_of_var))
    constr_vec <- c(constr_vec, rep(0, number_of_var))
    constr_dir <- c(constr_dir, rep(">=", number_of_var))
    
    stochastic_dominance_optimal <- 1:number_of_acts
    
    for (i in 1:number_of_acts) {
      other_acts <- setdiff(1:number_of_acts, i)
      for (k in 1:(number_of_acts - 1)) {
        constr_mat_ik <- constr_mat
        constr_vec_ik <- constr_vec
        constr_dir_ik <- constr_dir
        utility_table_ik <- utility_table[c(i, other_acts[k]), ]
        for (x in 1:2) {
          for (j in 1:number_of_states) {
            for (y in x:2) {
              compare_same <- x == y
              if (compare_same && j == number_of_states) {
                next
              }
              for (l in (compare_same * j + 1):number_of_states) {
                if (x != y || j != l) {
                  if (utility_table_ik[x, j] > utility_table_ik[y, l]) {
                    constr_mat_ik <- rbind(constr_mat_ik, rep(0, number_of_var))
                    constr_mat_ik[nrow(constr_mat_ik), 1 + (x - 1) * number_of_states + j] <- -1
                    constr_mat_ik[nrow(constr_mat_ik), 1 + (y - 1) * number_of_states + l] <- 1
                    constr_mat_ik[nrow(constr_mat_ik), 1] <- 1
                    constr_dir_ik <- c(constr_dir_ik, "<=")
                    constr_vec_ik <- c(constr_vec_ik, 0)
                  }
                  else if (utility_table_ik[x, j] < utility_table_ik[y, l]) {
                    constr_mat_ik <- rbind(constr_mat_ik, rep(0, number_of_var))
                    constr_mat_ik[nrow(constr_mat_ik), 1 + (x - 1) * number_of_states + j] <- 1
                    constr_mat_ik[nrow(constr_mat_ik), 1 + (y - 1) * number_of_states + l] <- -1
                    constr_mat_ik[nrow(constr_mat_ik), 1] <- 1
                    constr_dir_ik <- c(constr_dir_ik, "<=")
                    constr_vec_ik <- c(constr_vec_ik, 0)
                  }
                  else {
                    constr_mat_ik <- rbind(constr_mat_ik, rep(0, number_of_var))
                    constr_mat_ik[nrow(constr_mat_ik), 1 + (x - 1) * number_of_states + j] <- 1
                    constr_mat_ik[nrow(constr_mat_ik), 1 + (y - 1) * number_of_states + l] <- -1
                    constr_dir_ik <- c(constr_dir_ik, "==")
                    constr_vec_ik <- c(constr_vec_ik, 0)
                  }
                }
              }
            }
          }
        }
        if (is.null(priori)) {
          constr_vec_ik <- c(constr_vec_ik, rep(0, nrow(extreme_points)))
          
          if (mode == "utility") {
            constr_dir_ik <- c(constr_dir_ik, rep(">=", nrow(extreme_points)))
          }
          else if (mode == "loss") {
            constr_dir_ik <- c(constr_dir_ik, rep("<=", nrow(extreme_points)))
          }
        }
        else {
          constr_vec_ik <- c(constr_vec_ik, 0)
          
          if (mode == "utility") {
            constr_dir_ik <- c(constr_dir_ik, ">=")
          }
          else if (mode == "loss") {
            constr_dir_ik <- c(constr_dir_ik, "<=")
          }
        }
        objective <- c(1, rep(0, number_of_var - 1))
        if (is.null(priori)) {
          for (j in 1:nrow(extreme_points)) {
            constr_mat_ik <- rbind(constr_mat_ik, c(0, extreme_points[j, ], (-1) * extreme_points[j, ]))
          }
        }
        else {
          constr_mat_ik <- rbind(constr_mat_ik, c(0, priori, (-1) * priori))
        }
        
        optimization <- lp("max", objective, constr_mat_ik, constr_dir_ik, constr_vec_ik)
        if (round(optimization$objval, 10) == 0) {
          stochastic_dominance_optimal <- setdiff(stochastic_dominance_optimal, i)
          break
        }
      }
    }
    output <- rbind(utility_table[stochastic_dominance_optimal, ])
    row.names(output) <- row.names(utility_table)[stochastic_dominance_optimal]
    return(output)
  }
}

# function to compute the optimal acts with respect to Statistical Preference 
statistical_preference <- function(panel, mode = c("utility","loss"), mode2 = c("joint","pairwise"), priori = NULL, optimism = 0, filter_admissible = TRUE, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = ncol(panel), ncol = 2, byrow = TRUE)) {
  # check panel to be a non-trivial utility table with no missing values
  assert_matrix(panel, min.rows =  2, min.cols = 2)
  assert_numeric(panel, any.missing =  FALSE)
  
  # mode must be one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  # mode2 must be one of 'joint', 'pairwise'
  mode2 <- match.arg(mode2)
  
  # check if optimism is a valid parameter
  check_normalized_parameter(optimism)
  
  # check if 'filter_admissible' is a single logical value
  assert_flag(filter_admissible)
  
  # requirements concerning the optional priori distribution
  if (!is.null(priori)) {
    check_priori_requirements(panel,priori)
  }
  
  number_of_states <- ncol(panel)
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  # if no priori is given, use the extreme points from the probability requirements instead
  if (is.null(priori)) {
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    if (nrow(extreme_points) == 1) {
      priori <- extreme_points
    }
  }
  
  if (filter_admissible == TRUE) {
    admissible_acts <- exclude_dominated(panel, mode, FALSE, FALSE)
    utility_table <- rbind(panel[admissible_acts, ])
    row.names(utility_table) <- admissible_acts
  }
  else {
    utility_table <- panel
    row.names(utility_table) <- 1:nrow(panel)
  }
  
  number_of_acts <- nrow(utility_table)
  if (number_of_acts == 1) {
    return(utility_table)
  }
  
  if (mode2 == "joint") {
    if (!is.null(priori)) {
      # if there is a priori simply compute for each act the sum of the probabilities for the states where the respective act is one of the optimal acts
      criteria <- data.frame(row.names = 1:number_of_acts)
      criteria$acts <- row.names(utility_table)
      criteria$value <- 0
      if (mode == "utility") {
        for (j in 1:number_of_states) {
          max_j <- max(utility_table[, j])
          for (i in 1:number_of_acts) {
            if (utility_table[i, j] == max_j) {
              criteria$value[i] <- criteria$value[i] + priori[j]
            }
          }
        }
        # The maximal criteria value defines the optimal acts with respect to (Imprecise) Joint Stochastic Dominance
        maximum <- max(criteria$value)
        optimal <- row.names(utility_table)[criteria$value == maximum]
        output <- data.frame(row.names = 1:length(optimal))
        output$action <- optimal
        output <- list(output, maximum)
        return(output)
      }
      if (mode == "loss") {
        # for loss just consider the minimum as optimal instead of the maximum
        for (j in 1:number_of_states) {
          min_j <- min(utility_table[, j])
          for (i in 1:number_of_acts) {
            if (utility_table[i, j] == min_j) {
              criteria$value[i] <- criteria$value[i] + priori[j]
            }
          }
        }
        maximum <- max(criteria$value)
        optimal <- row.names(utility_table)[criteria$value == maximum]
        output <- data.frame(row.names = 1:length(optimal))
        output$action <- optimal
        output <- list(output, maximum)
        return(output)
      }
    }
    else {
      # if there are several extreme points instead of a single priori one needs to compute the acts' probabilities to be optimal for each one of the extreme points to find the best and worst case probabilities
      extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
      criteria <- data.frame(row.names = 1:number_of_acts)
      criteria$acts <- row.names(utility_table)
      criteria$worst_case <- Inf
      criteria$best_case <- -Inf
      if (mode == "utility") {
        for (l in 1:nrow(extreme_points)) {
          criteria_tmp <- data.frame(row.names = 1:number_of_acts)
          criteria_tmp$acts <- row.names(utility_table)
          criteria_tmp$value <- 0
          for (j in 1:number_of_states) {
            max_j <- max(utility_table[, j])
            for (i in 1:number_of_acts) {
              if (utility_table[i, j] == max_j) {
                criteria_tmp$value[i] <- criteria_tmp$value[i] + extreme_points[l, j]
              }
            }
          }
          for (i in 1:number_of_acts) {
            if (criteria_tmp$value[i] < criteria$worst_case[i]) {
              criteria$worst_case[i] <- criteria_tmp$value[i]
            }
            if (criteria_tmp$value[i] > criteria$best_case[i]) {
              criteria$best_case[i] <- criteria_tmp$value[i]
            }
          }
        }
        # Optimism works as weight between best and worst case like for the Hansen-Hurwitz-criterion
        criteria$value <- optimism * criteria$best_case + (1 - optimism) * criteria$worst_case
        maximum <- max(criteria$value)
        optimal <- row.names(utility_table)[criteria$value == maximum]
        output <- data.frame(row.names = 1:length(optimal))
        output$action <- optimal
        output <- list(output, maximum)
        return(output)
      }
      else if (mode == "loss") {
        # consider minimal loss instead of maximal utility
        for (l in 1:nrow(extreme_points)) {
          criteria_tmp <- data.frame(row.names = 1:number_of_acts)
          criteria_tmp$acts <- row.names(utility_table)
          criteria$worst_case <- Inf
          criteria$best_case <- -Inf
          for (j in 1:number_of_states) {
            min_j <- min(utility_table[, j])
            for (i in 1:number_of_acts) {
              if (utility_table[i, j] == min_j) {
                criteria_tmp$value[i] <- criteria_tmp$value[i] + extreme_points[l, j]
              }
            }
          }
          for (i in 1:number_of_acts) {
            if (criteria_tmp$value[i] < criteria$worst_case[i]) {
              criteria$worst_case[i] <- criteria_tmp$value[i]
            }
            if (criteria_tmp$value[i] > criteria$best_case[i]) {
              criteria$best_case[i] <- criteria_tmp$value[i]
            }
          }
        }
        criteria$value <- optimism * criteria$best_case + (1 - optimism) * criteria$worst_case
        maximum <- max(criteria$value)
        optimal <- row.names(utility_table)[criteria$value == maximum]
        output <- data.frame(row.names = 1:length(optimal))
        output$action <- optimal
        output <- list(output, maximum)
        return(output)
      }
    }
  }
  else if (mode2 == "pairwise") {
    # The function is basically the same as the Joint version
    # Instead of computing the probability for an act do be optimal among all other acts, one simply just compares for two acts, which one is more likely to be optimal
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    statistical_preference_optimal <- 1:number_of_acts
    if (!(is.null(priori))) {
      if (mode == "utility") {
        for (i in 1:(number_of_acts - 1)) {
          for (k in (i + 1):number_of_acts) {
            prob_i_greater_k <- 0
            prob_k_greater_i <- 0
            for (j in 1:number_of_states) {
              if (utility_table[i, j] > utility_table[k, j]) {
                prob_i_greater_k <- prob_i_greater_k + priori[j]
              }
              else if (utility_table[i, j] < utility_table[k, j]) {
                prob_k_greater_i <- prob_k_greater_i + priori[j]
              }
              else {
                prob_i_greater_k <- prob_i_greater_k + priori[j]
                prob_k_greater_i <- prob_k_greater_i + priori[j]
              }
            }
            if (prob_i_greater_k > prob_k_greater_i) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, k)
            }
            else if (prob_k_greater_i > prob_i_greater_k) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, i)
            }
          }
        }
        output <- rbind(utility_table[statistical_preference_optimal, ])
        row.names(output) <- row.names(utility_table)[statistical_preference_optimal]
        return(output)
      }
      else if (mode == "loss") {
        for (i in 1:(number_of_acts - 1)) {
          for (k in (i + 1):number_of_acts) {
            prob_i_greater_k <- 0
            prob_k_greater_i <- 0
            for (j in 1:number_of_states) {
              if (utility_table[i, j] > utility_table[k, j]) {
                prob_i_greater_k <- prob_i_greater_k + priori[j]
              }
              else if (utility_table[i, j] < utility_table[k, j]) {
                prob_k_greater_i <- prob_k_greater_i + priori[j]
              }
              else {
                prob_i_greater_k <- prob_i_greater_k + priori[j]
                prob_k_greater_i <- prob_k_greater_i + priori[j]
              }
            }
            if (prob_i_greater_k < prob_k_greater_i) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, k)
            }
            else if (prob_k_greater_i < prob_i_greater_k) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, i)
            }
          }
        }
        output <- rbind(utility_table[statistical_preference_optimal, ])
        row.names(output) <- row.names(utility_table)[statistical_preference_optimal]
        return(output)
      }
    }
    else {
      statistical_preference_optimal <- 1:number_of_acts
      if (mode == "utility") {
        for (i in 1:(number_of_acts - 1)) {
          for (k in (i + 1):number_of_acts) {
            save_worst_probs <- c(Inf, Inf)
            save_best_probs <- c(-Inf, -Inf)
            for (l in 1:nrow(extreme_points)) {
              prob_i_greater_k <- 0
              prob_k_greater_i <- 0
              for (j in 1:number_of_states) {
                if (utility_table[i, j] > utility_table[k, j]) {
                  prob_i_greater_k <- prob_i_greater_k + extreme_points[l, j]
                }
                else if (utility_table[i, j] < utility_table[k, j]) {
                  prob_k_greater_i <- prob_k_greater_i + extreme_points[l, j]
                }
                else {
                  prob_i_greater_k <- prob_i_greater_k + extreme_points[l, j]
                  prob_k_greater_i <- prob_k_greater_i + extreme_points[l, j]
                }
              }
              if (prob_i_greater_k < save_worst_probs[1]) {
                save_worst_probs[1] <- prob_i_greater_k
              }
              if (prob_i_greater_k > save_best_probs[1]) {
                save_best_probs[1] <- prob_i_greater_k
              }
              if (prob_k_greater_i < save_worst_probs[2]) {
                save_worst_probs[2] <- prob_k_greater_i
              }
              if (prob_k_greater_i > save_best_probs[2]) {
                save_best_probs[2] <- prob_k_greater_i
              }
            }
            weighted_probs <- save_best_probs * optimism + save_worst_probs * (1 - optimism)
            if (weighted_probs[1] > weighted_probs[2]) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, k)
            }
            else if (weighted_probs[1] < weighted_probs[2]) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, i)
            }
          }
        }
        output <- rbind(utility_table[statistical_preference_optimal, ])
        row.names(output) <- row.names(utility_table)[statistical_preference_optimal]
        return(output)
      }
      else if (mode == "loss") {
        for (i in 1:(number_of_acts - 1)) {
          for (k in (i + 1):number_of_acts) {
            save_worst_probs <- c(Inf, Inf)
            save_best_probs <- c(-Inf, -Inf)
            for (l in 1:nrow(extreme_points)) {
              prob_i_greater_k <- 0
              prob_k_greater_i <- 0
              for (j in 1:number_of_states) {
                if (utility_table[i, j] > utility_table[k, j]) {
                  prob_i_greater_k <- prob_i_greater_k + extreme_points[l, j]
                }
                else if (utility_table[i, j] < utility_table[k, j]) {
                  prob_k_greater_i <- prob_k_greater_i + extreme_points[l, j]
                }
                else {
                  prob_i_greater_k <- prob_i_greater_k + extreme_points[l, j]
                  prob_k_greater_i <- prob_k_greater_i + extreme_points[l, j]
                }
              }
              if (prob_k_greater_i < save_worst_probs[1]) {
                save_worst_probs[1] <- prob_k_greater_i
              }
              if (prob_k_greater_i > save_best_probs[1]) {
                save_best_probs[1] <- prob_k_greater_i
              }
              if (prob_i_greater_k < save_worst_probs[2]) {
                save_worst_probs[2] <- prob_i_greater_k
              }
              if (prob_i_greater_k > save_best_probs[2]) {
                save_best_probs[2] <- prob_i_greater_k
              }
            }
            weighted_probs <- save_best_probs * optimism + save_worst_probs * (1 - optimism)
            if (weighted_probs[1] > weighted_probs[2]) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, k)
            }
            else if (weighted_probs[1] < weighted_probs[2]) {
              statistical_preference_optimal <- setdiff(statistical_preference_optimal, i)
            }
          }
        }
        output <- rbind(utility_table[statistical_preference_optimal, ])
        row.names(output) <- row.names(utility_table)[statistical_preference_optimal]
        return(output)
      }
    }
  }
}

#### functions for decision making based on preference systems #####

# function to construct the basic constraint matrix and its corresponding contraint vector and direction vector for the following criteria
construct_preference_system_constraints <- function(number_of_acts, number_of_states, r1_strict, r1_indifferent = NULL, r2_strict = NULL, r2_indifferent = NULL) {
  
  # necessary to calculate indices 
  state_factor <- 10^(floor(logb(number_of_states, 10)) + 1)
  
  # basic requirements on optimization parameters (representing 0-1-normalized utilities)
  number_of_var <- 1 + number_of_acts * number_of_states
  constr_mat <- diag(1, number_of_var)
  constr_mat <- rbind(constr_mat, constr_mat)
  constr_vec <- c(rep(0, number_of_var), rep(1, number_of_var))
  constr_dir <- c(rep(">=", number_of_var), rep("<=", number_of_var))
  
  # elements in the strict part of R1 must differ at least by an optimization parameter representing epsilon
  for (i in 1:length(r1_strict)) {
    vector_i <- r1_strict[[i]]
    for (j in 1:(length(vector_i) - 1)) {
      constr_mat <- rbind(constr_mat, rep(0, (number_of_var)))
      indx_1 <- round((floor(vector_i[j]) - 1) * number_of_states + vector_i[j] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_1] <- -1
      indx_2 <- round((floor(vector_i[j + 1]) - 1) * number_of_states + vector_i[j + 1] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_2] <- 1
      constr_mat[nrow(constr_mat), ncol(constr_mat)] <- 1
      constr_vec <- c(constr_vec, 0)
      constr_dir <- c(constr_dir, "<=")
    }
  }
  
  # elements in the indifferent part of R1 must be equal
  if (!is.null(r1_indifferent)) {
    for (i in 1:length(r1_indifferent)) {
      vector_i <- r1_indifferent[[i]]
      for (j in 1:(length(vector_i) - 1)) {
        constr_mat <- rbind(constr_mat, rep(0, (number_of_var)))
        indx_1 <- round((floor(vector_i[j]) - 1) * number_of_states + vector_i[j] %% 1 * state_factor)
        constr_mat[nrow(constr_mat), indx_1] <- -1
        indx_2 <- round((floor(vector_i[j + 1]) - 1) * number_of_states + vector_i[j + 1] %% 1 * state_factor)
        constr_mat[nrow(constr_mat), indx_2] <- 1
        constr_vec <- c(constr_vec, 0)
        constr_dir <- c(constr_dir, "==")
      }
    }
  }
  
  # elements in the strict part of R2 must differ at least by an optimization parameter representing epsilon
  if (!is.null(r2_strict)) {
    r2_strict_matrix <- matrix(0, 0, 4)
    for (i in 1:length(r2_strict)) {
      r2_strict_matrix <- rbind(r2_strict_matrix, r2_strict[[i]])
    }
    
    r2_data <- r2_strict_matrix %>% as.data.frame()
    
    for (i in 1:nrow(r2_data)) {
      vector_i <- r2_strict_matrix[i, ]
      constr_mat <- rbind(constr_mat, rep(0, (number_of_var)))
      indx_1 <- round((floor(vector_i[1]) - 1) * number_of_states + vector_i[1] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_1] <- -1
      indx_2 <- round((floor(vector_i[2]) - 1) * number_of_states + vector_i[2] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_2] <- constr_mat[nrow(constr_mat), indx_2] + 1
      indx_3 <- round((floor(vector_i[3]) - 1) * number_of_states + vector_i[3] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_3] <- constr_mat[nrow(constr_mat), indx_3] + 1
      indx_4 <- round((floor(vector_i[4]) - 1) * number_of_states + vector_i[4] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_4] <- constr_mat[nrow(constr_mat), indx_4] - 1
      constr_mat[nrow(constr_mat), ncol(constr_mat)] <- 1
      constr_vec <- c(constr_vec, 0)
      constr_dir <- c(constr_dir, "<=")
    }
  }
  
  # elements in the indifferent part of R2 must be equal
  if (!is.null(r2_indifferent)) {
    r2_indifferent_matrix <- matrix(0, 0, 4)
    for (i in 1:length(r2_indifferent)) {
      r2_indifferent_matrix <- rbind(r2_indifferent_matrix, r2_indifferent[[i]])
    }
    
    r2_data <- r2_indifferent_matrix %>% as.data.frame()
    
    for (i in 1:nrow(r2_data)) {
      vector_i <- r2_indifferent_matrix[i, ]
      constr_mat <- rbind(constr_mat, rep(0, (number_of_var)))
      indx_1 <- round((floor(vector_i[1]) - 1) * number_of_states + vector_i[1] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_1] <- -1
      indx_2 <- round((floor(vector_i[2]) - 1) * number_of_states + vector_i[2] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_2] <- constr_mat[nrow(constr_mat), indx_2] + 1
      indx_3 <- round((floor(vector_i[3]) - 1) * number_of_states + vector_i[3] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_3] <- constr_mat[nrow(constr_mat), indx_3] + 1
      indx_4 <- round((floor(vector_i[4]) - 1) * number_of_states + vector_i[4] %% 1 * state_factor)
      constr_mat[nrow(constr_mat), indx_4] <- constr_mat[nrow(constr_mat), indx_4] - 1
      constr_vec <- c(constr_vec, 0)
      constr_dir <- c(constr_dir, "==")
    }
  }
  return(list(constr_mat,constr_vec,constr_dir))
}

# function to evaluate if a preference system is consistent
check_preference_system <- function(number_of_acts, number_of_states, r1_strict, r1_indifferent = NULL, r2_strict = NULL, r2_indifferent = NULL) {
  
  # check if input requirements on relations are fulfilled
  state_factor <- check_preference_relations(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent)
  
  # calculate number of variables in optimization problem
  number_of_var <- 1 + number_of_acts * number_of_states
  
  # construct constraints out of the most basic requirements
  constraints <- construct_preference_system_constraints(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent)
  constr_mat <- constraints[[1]]
  constr_vec <- constraints[[2]]
  constr_dir <- constraints[[3]]
  
  all_coordinates <- c()
  for (i in 1:number_of_acts) {
    all_coordinates <- c(all_coordinates, i + (1:number_of_states) / state_factor)
  }
  
  objective <- c(rep(0, number_of_var - 1), 1)
  optimization <- lp("max", objective, constr_mat, constr_dir, constr_vec)
  
  output_matrix <- matrix(optimization$solution[-length(optimization$solution)], nrow = number_of_acts, byrow = TRUE)
  rownames(output_matrix) <- 1:number_of_acts
  
  return(list(output_matrix, optimization$objval))
}

#function to compute Generalized Interval Expectation
generalized_interval_expectation <- function(number_of_acts, number_of_states, r1_strict, r1_indifferent = NULL, r2_strict = NULL, r2_indifferent = NULL, delta = NULL, a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = number_of_states, ncol = 2, byrow = TRUE)) {
  
  # check if input requirements on relations are fullfilled
  state_factor <- check_preference_relations(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent)
  
  # check if delta is a valid parameter
  check_normalized_parameter(delta)
  
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  all_coordinates <- c()
  for (i in 1:number_of_acts) {
    all_coordinates <- c(all_coordinates, i + (1:number_of_states) / state_factor)
  }
  
  # calculate number of variables in optimization problem
  number_of_var <- 1 + number_of_acts * number_of_states
  
  # construct constraints out of the most basic requirements
  constraints <- construct_preference_system_constraints(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent)
  constr_mat <- constraints[[1]]
  constr_vec <- constraints[[2]]
  constr_dir <- constraints[[3]]
  
  # set epsilon to delta
  constr_mat <- rbind(constr_mat, c(rep(0, number_of_var - 1), 1))
  constr_vec <- c(constr_vec, delta)
  constr_dir <- c(constr_dir, "==")
  
  # find the act-state-interactions with the highest utility
  maximal_utility <- c()
  for (i in 1:length(r1_strict)) {
    vector_i <- r1_strict[[i]]
    maximum_i <- vector_i[1]
    is_max <- TRUE
    for (j in setdiff(1:length(r1_strict), i)) {
      vector_j <- r1_strict[[j]]
      if (maximum_i %in% vector_j) {
        if (maximum_i != vector_j[1]) {
          is_max <- FALSE
          break
        }
      }
    }
    if (is_max) {
      done <- FALSE
      if (!is.null(r1_indifferent)) {
        for (j in 1:length(r1_indifferent)) {
          vector_j <- r1_indifferent[[j]]
          if (maximum_i %in% vector_j) {
            maximal_utility <- c(maximal_utility, vector_j)
            done <- TRUE
          }
        }
      }
      if (done == FALSE) {
        maximal_utility <- maximum_i
      }
      break
    }
  }
  
  # find the act-state-interactions with the lowest utility
  minimal_utility <- c()
  for (i in 1:length(r1_strict)) {
    vector_i <- r1_strict[[i]]
    minimum_i <- vector_i[length(vector_i)]
    is_min <- TRUE
    for (j in setdiff(1:length(r1_strict), i)) {
      vector_j <- r1_strict[[j]]
      if (minimum_i %in% vector_j) {
        if (minimum_i != vector_j[length(vector_j)]) {
          is_min <- FALSE
          break
        }
      }
    }
    if (is_min) {
      done <- FALSE
      if (!is.null(r1_indifferent)) {
        for (j in 1:length(r1_indifferent)) {
          vector_j <- r1_indifferent[[j]]
          if (minimum_i %in% vector_j) {
            minimal_utility <- c(minimal_utility, vector_j)
            done <- TRUE
          }
        }
      }
      if (done == FALSE) {
        minimal_utility <- minimum_i
      }
      break
    }
  }
  
  # set the highest utility to 1
  for (i in 1:length(maximal_utility)) {
    indx_i <- round((floor(maximal_utility[i]) - 1) * number_of_states + maximal_utility[i] %% 1 * state_factor)
    constr_mat <- rbind(constr_mat, rep(0, number_of_var))
    constr_mat[nrow(constr_mat), indx_i] <- 1
    constr_vec <- c(constr_vec, 1)
    constr_dir <- c(constr_dir, "==")
  }
  
  # set the lowest utility to 0
  for (i in 1:length(minimal_utility)) {
    indx_i <- round((floor(minimal_utility[i]) - 1) * number_of_states + minimal_utility[i] %% 1 * state_factor)
    constr_mat <- rbind(constr_mat, rep(0, number_of_var))
    constr_mat[nrow(constr_mat), indx_i] <- 1
    constr_vec <- c(constr_vec, 0)
    constr_dir <- c(constr_dir, "==")
  }
  
  # basic structure of output intervals
  interval_expectation <- matrix(NA, nrow = number_of_acts, ncol = 2)
  rownames(interval_expectation) <- 1:number_of_acts
  interval_expectation[, 1] <- Inf
  interval_expectation[, 2] <- -Inf
  
  # compute the set of extreme points
  extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
  
  for (i in 1:number_of_acts) {
    for (j in 1:nrow(extreme_points)) {
      # minimize and maximize the utility expectation for every extreme point
      # this will define the interval induced by the possible utilities for the preference system
      objective <- rep(0, number_of_var)
      objective[((i - 1) * number_of_states + 1):(i * number_of_states)] <- extreme_points[j, ]
      minimization <- lp("min", objective, constr_mat, constr_dir, constr_vec)$objval
      if (minimization < interval_expectation[i, 1]) {
        interval_expectation[i, 1] <- minimization
      }
      maximization <- lp("max", objective, constr_mat, constr_dir, constr_vec)$objval
      if (maximization > interval_expectation[i, 2]) {
        interval_expectation[i, 2] <- maximization
      }
    }
  }
  if (max(interval_expectation[, 2]) == 0) {
    stop(paste("There is no solution for 'delta'", "=", delta))
  }
  else {
    return(interval_expectation)
  }
}

# function to compute optimal acts in preference systems with respect to Global Admissibility
ps_global_admissibility <- function(number_of_acts, number_of_states, r1_strict, r1_indifferent = NULL, r2_strict = NULL, r2_indifferent = NULL, mode = c("utility","loss"), mode2 = c("AM","A","M","dominant"), a1 = NULL, b1 = NULL, a2 = NULL, b2 = NULL, ordinal_structure = NULL, boundaries = matrix(c(0, 1), nrow = number_of_states, ncol = 2, byrow = TRUE)) {
  
  # check if input requirements on relations are fullfilled
  state_factor <- check_preference_relations(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent)
  
  #check if mode is one of 'utility', 'loss'
  mode <- match.arg(mode)
  
  #check if mode2 is one of "AM","A","M","dominant"
  mode2 <- match.arg(mode2)
  
  # check if probability input variables are consistent and if so use induced boundary matrix
  boundaries <- check_probability_consistency(number_of_states, a1, a2, b1, b2, boundaries, ordinal_structure)
  
  all_coordinates <- c()
  for (i in 1:number_of_acts) {
    all_coordinates <- c(all_coordinates, i + (1:number_of_states) / state_factor)
  }
  
  # calculate number of variables in optimization problem
  number_of_var <- 1 + number_of_acts * number_of_states
  
  # construct constraints out of the most basic requirements
  constraints <- construct_preference_system_constraints(number_of_acts, number_of_states, r1_strict, r1_indifferent, r2_strict, r2_indifferent)
  constr_mat <- constraints[[1]]
  constr_vec <- constraints[[2]]
  constr_dir <- constraints[[3]]
  
  if (mode2 == "AM") {
    admissible <- vector("integer", 0)
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    objective <- c(rep(0, number_of_var - 1), 1)
    constr_vec <- c(constr_vec, rep(0, number_of_acts - 1))
    if (mode == "utility") {
      constr_dir <- c(constr_dir, rep(">=", number_of_acts - 1))
    }
    else if (mode == "loss") {
      constr_dir <- c(constr_dir, rep("<=", number_of_acts - 1))
    }
    for (i in 1:number_of_acts) {
      for (j in 1:nrow(extreme_points)) {
        # for each extreme point solve the following optimization problem
        constr_mat_iteration <- constr_mat
        for (i2 in 1:number_of_acts) {
          if (i != i2) {
            # constraints to compare the expected utility of act i with every other act for extreme point j
            constr_mat_iteration <- rbind(constr_mat_iteration, rep(0, number_of_var))
            constr_mat_iteration[nrow(constr_mat_iteration), ((i - 1) * number_of_states + 1):(i * number_of_states)] <- extreme_points[j, ]
            constr_mat_iteration[nrow(constr_mat_iteration), ((i2 - 1) * number_of_states + 1):(i2 * number_of_states)] <- (-1) * extreme_points[j, ]
          }
        }
        # if one can find an extreme point, for which act there is a utility for which act i is the best act according to utility expectation, then i is AM-admissible
        optimization <- lp("max", objective, constr_mat_iteration, constr_dir, constr_vec)
        if (optimization$objval > 0) {
          admissible <- c(admissible, i)
          break
        }
      }
    }
    return(admissible)
  }
  else if (mode2 == "A") {
    admissible <- vector("integer", 0)
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    objective <- c(rep(0, number_of_var - 1), 1)
    constr_vec <- c(constr_vec, rep(0, nrow(extreme_points) * (number_of_acts - 1)))
    if (mode == "utility") {
      constr_dir <- c(constr_dir, rep(">=", nrow(extreme_points) * (number_of_acts - 1)))
    }
    else if (mode == "loss") {
      constr_dir <- c(constr_dir, rep("<=", nrow(extreme_points) * (number_of_acts - 1)))
    }
    for (i in 1:number_of_acts) {
      constr_mat_iteration <- constr_mat
      # for each extreme point and each other act add the following constraints:
      for (j in 1:nrow(extreme_points)) {
        i2 <- 1
        for (i2 in 1:number_of_acts) {
          if (i != i2) {
            # comparison of expected utility of act i with every other act
            constr_mat_iteration <- rbind(constr_mat_iteration, rep(0, number_of_var))
            constr_mat_iteration[nrow(constr_mat_iteration), ((i - 1) * number_of_states + 1):(i * number_of_states)] <- extreme_points[j, ]
            constr_mat_iteration[nrow(constr_mat_iteration), ((i2 - 1) * number_of_states + 1):(i2 * number_of_states)] <- (-1) * extreme_points[j, ]
          }
        }
      }
      # if the maximum value of the optimization problem is > 0 then i is A-admissible
      optimization <- lp("max", objective, constr_mat_iteration, constr_dir, constr_vec)
      if (optimization$objval > 0) {
        admissible <- c(admissible, i)
      }
    }
    return(admissible)
  }
  else if (mode2 == "M") {
    admissible <- vector("integer", 0)
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    for (i in 1:number_of_acts) {
      for (j in 1:nrow(extreme_points)) {
        is_admissible <- FALSE
        for (i2 in 1:number_of_acts) {
          if (i2 != i) {
            # check for every extreme point if there is a utility function for which act i2 can be strictly better than act i
            objective <- rep(0, number_of_var)
            objective[((i2 - 1) * number_of_states + 1):(i2 * number_of_states)] <- extreme_points[j, ]
            objective[((i - 1) * number_of_states + 1):(i * number_of_states)] <- (-1) * extreme_points[j, ]
            
            if (mode == "utility") {
              optimization <- lp("max", objective, constr_mat, constr_dir, constr_vec)
              # if i2 is strictly better for any utility function, i cannot be M-admissible
              if (optimization$objval > 0) {
                break
              }
              else if (i2 == number_of_acts) {
                is_admissible <- TRUE
              }
            }
            else if (mode == "loss") {
              optimization <- lp("min", objective, constr_mat, constr_dir, constr_vec)
              # if i2 is strictly better for any loss function, i cannot be M-admissible
              if (optimization$objval < 0) {
                break
              }
              else if (i2 == number_of_acts) {
                is_admissible <- TRUE
              }
            }
          }
        }
        if (is_admissible == TRUE) {
          admissible <- c(admissible, i)
          break
        }
      }
    }
    return(admissible)
  }
  else if (mode2 == "dominant") {
    not_admissible <- c()
    extreme_points <- extreme_point_finder_rcdd(number_of_states, a1, b1, a2, b2, boundaries, ordinal_structure)
    for (i in 1:number_of_acts) {
      for (i2 in 1:number_of_acts) {
        if (i != i2) {
          for (j in 1:nrow(extreme_points)) {
            # check for every extreme point if there is a utility function for which act i is better than act i2 for every utility
            objective <- rep(0, number_of_var)
            objective[((i2 - 1) * number_of_states + 1):(i2 * number_of_states)] <- extreme_points[j, ]
            objective[((i - 1) * number_of_states + 1):(i * number_of_states)] <- (-1) * extreme_points[j, ]
            
            if (mode == "utility") {
              optimization <- lp("max", objective, constr_mat, constr_dir, constr_vec)
              # if there is an extreme point for which one can find a utility for which the expectation of act i is strictly smaller, then i is not AM-dominant
              if (optimization$objval > 0) {
                not_admissible <- c(not_admissible, i)
                break
              }
            }
            else if (mode == "loss") {
              optimization <- lp("min", objective, constr_mat, constr_dir, constr_vec)
              # if there is an extreme point for which one can find a loss for which the expectation of act i is strictly greater, than i is not AM-dominant
              if (optimization$objval < 0) {
                not_admissible <- c(not_admissible, i)
                break
              }
            }
          }
        }
      }
    }
    return(setdiff(1:number_of_acts, not_admissible))
  }
}
