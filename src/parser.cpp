/*------------------------------------------------------------------------*/
/*! \file parser.cpp
    \brief contains functions necessary to parse the AIG

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#include "parser.h"
/*------------------------------------------------------------------------*/

bool match_and(unsigned lhs, unsigned rhs0, unsigned rhs1) {
  if (lhs == aiger_false) return 0;
  if (aiger_sign(lhs)) return 0;
  assert(lhs != aiger_true);

  aiger_and * and1 = is_model_and(lhs);
  if (!and1) return 0;
  if (and1->rhs0 == rhs0 && and1->rhs1 == rhs1) return 1;
  if (and1->rhs0 == rhs1 && and1->rhs1 == rhs0) return 1;
  return 0;
}

/*------------------------------------------------------------------------*/
void determine_input_order() {
  unsigned s0 = 0, sl = NN-1;
  if (match_and(
        slit(0),
        get_model_inputs_lit(0),
        get_model_inputs_lit(1))) {
    a0 = 0, al = NN-2, ainc = 2;
    b0 = 1, bl = NN-1, binc = 2;
    msg("assuming ordering as in BTOR generated benchmarks");
  } else {
    a0 = 0, al = NN/2-1,   ainc = 1;
    b0 = NN/2, bl = NN-1, binc = 1;
    msg("assuming ordering as in the ABC generated or AOKI benchmarks");
  }
  if (verbose >= 2) {
    if (NN == 2) {
      msg("a[0] = input[%d]", a0);
      msg("b[0] = input[%d]", b0);
      msg("s[0] = output[%d]", s0);
    } else if (NN == 4) {
      msg("(a[0], a[1]) =(input[%d], input[%d])", a0, al);
      msg("(b[0], b[1]) =(input[%d], input[%d])", b0, bl);
      msg("(s[0], ..., s[3]) =(output[%d], ..., output[%d])", s0, sl);
    } else if (NN == 6) {
      msg("(a[0], a[1], a[2]) =(input[%d], input[%d], input[%d])",
        a0, a0 + ainc, al);
      msg("(b[0], b[1], b[2]) =(input[%d], input[%d], input[%d])",
        b0, b0 + binc, bl);
      msg("(s[0], ..., s[5]) =(output[%d], ..., output[%d])", s0, sl);
    } else {
      msg("(a[0], a[1], ..., a[%d]) =(input[%d], input[%d], ..., input[%d])",
        NN/2-1, a0, a0 + ainc, al);
      msg("(b[0], b[1], ..., b[%d]) =(input[%d], input[%d], ..., input[%d])",
        NN/2-1, b0, b0 + binc, bl);
      msg("(s[0], ..., s[%d]) =(output[%d], ..., output[%d])",
        NN-1, s0, sl);
    }
  }
}

/*------------------------------------------------------------------------*/

void init_aiger_with_checks() {
  if (get_model_num_latches()) die("can not handle latches");
  if (!get_model_num_inputs()) die("no inputs");
  if ((get_model_num_inputs() & 1)) die("odd number of inputs");
  if (!get_model_num_outputs()) die("no outputs");
  if (get_model_num_outputs() == get_model_num_inputs()) {
    M = get_model_maxvar() + 1;
    NN = get_model_num_outputs();
  }
  else  die("expected %u but got %u outputs",
      get_model_num_inputs(), get_model_num_outputs());


  msg("MILOA %u %u %u %u %u",
    get_model_maxvar(),
    get_model_num_inputs(),
    get_model_num_latches(),
    get_model_num_outputs(),
    get_model_num_ands());

  determine_input_order();
}

/*------------------------------------------------------------------------*/

void parse_aig(const char * input_name) {
  init_aig_parsing();

  msg("reading '%s'", input_name);
  const char * err = aiger_open_and_read_to_model(input_name);
  if (err) die("error parsing '%s': %s", input_name, err);

  init_aiger_with_checks();
}
