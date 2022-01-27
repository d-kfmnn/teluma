/*------------------------------------------------------------------------*/
/*! \file adder_identification.cpp
    \brief contains function to identify the final stage adder

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#include <list>

#include "adder_identification.h"
/*------------------------------------------------------------------------*/
// Local variables
Gate * carry_in;
std::vector<Gate*> carries;

static std::vector<Gate*> outputs;
/*------------------------------------------------------------------------*/

/**
    Checks whether all AIG outputs are used only once

    @return True if all AIG outputs are single gates
*/
static bool all_single_output() {
  for (unsigned i = 0; i < NN-1; i++) {
    Gate * n = gate(slit(i));
    if (n->parents_size() > 1) return 0;
  }
  return 1;
}

/*------------------------------------------------------------------------*/
/**
    Checks whether all AIG outputs are XOR gates

    @return True if all outputs in slices 1 to NN-2 are XOR gates
*/
static bool all_outputs_are_xor() {
  for (unsigned i = 1; i < NN-1; i++) {
    Gate * n = gate(slit(i));
    if (!n->get_xor_gate()) return 0;
  }
  return 1;
}

/*------------------------------------------------------------------------*/
/**
    If the output of slice 2 has more than 3 parents, than the carry-in
    of the final stage is the output of slice 0(in the aoki benchmarks.)

    @return False if output of slice 2 has more than 3 parents but output
    of slice 0 is single gate
*/
static bool slice_two_needs_carry_in_slice_zero() {
  Gate * out2 = gate(slit(2));
  Gate * out0 = gate(slit(0));
  if (out2->parents_size() > 3 && out0->parents_size() == 1) return 0;
  return 1;
}

/*------------------------------------------------------------------------*/
/**
    Checks whether the output of slice 0 is a possible carry-in for the
    final stage adder

    @return True if output of slice 0 has more than one parent.
*/
static bool cin_in_slice_0() {
  Gate * n = gate(slit(0));
  if (n->parents_size() > 1) return 1;
  return 0;
}

/*------------------------------------------------------------------------*/
/**
    Adds the gate n to the cins vector and sets it's slice to i

    @param n Gate* to be pushed
    @param push indicates whether carry is stored in carries array
*/
static void push_to_cins(Gate * n) {
  carries.push_back(n);
  carry_in = n;
  n->mark_fsa(2);
  if (verbose >= 2)  msg("identified carry %s", n->get_var_name());
}


/*------------------------------------------------------------------------*/
/**
    Identifies the carry out of the final stage adder
*/
static void identify_carry_out() {
  Gate * carry_out;
  Gate * largest_aig_output = gate(slit(NN-1));

  if (largest_aig_output->get_xor_gate() != 1) {
    carry_out = largest_aig_output;
  } else {
    Gate * l = xor_left_child(largest_aig_output);
    Gate * r = xor_right_child(largest_aig_output);
    carry_out = r->get_level() > l->get_level() ? r : l;
  }
  outputs.push_back(carry_out);
  carry_out->mark_fsa(2);
  carries.push_back(carry_out);
  if (verbose >= 3)  msg("identified carry out %s", carry_out->get_var_name());
}


/*------------------------------------------------------------------------*/
/**
    Identifies the propagate and generate gates of the final stage adder

    @return True if all checks succeeded
*/
bool identify_propagate_and_generate_gates() {
// slice NN-1 contains carry, slice 0 is no XOR
  for (int i = NN-2; i > 0; i--) {
    Gate * n = gate(slit(i));

    if (i == 2 && n->parents_size() > 3) {
      assert(gate(slit(0))->parents_size() > 1);

      outputs.push_back(n);
      outputs.push_back(gate(slit(1)));
      outputs.push_back(gate(slit(0)));

      n->mark_fsa_inp();
      gate(slit(1))->mark_fsa_inp();
      push_to_cins(gate(slit(0)));
      return 1;
    }

    Gate * internal_xor, *l = 0, *r = 0;
    if (i == 1 && n->parents_size() > 1) { internal_xor = n;
    } else {
      l = xor_left_child(n);
      r = xor_right_child(n);
      internal_xor = l->get_xor_gate() ? l : r;
    }

    if (internal_xor->parents_size() < 3) break;

    if (internal_xor->parents_size() == 3 && i < 3*((int) NN-1)/4
        && !cin_in_slice_0()) {
      if (all_single_output()) break;
      else if (!booth && !signed_mult) break;  // sp-ba-csv
    }

    internal_xor->mark_prop_gen_gate();
    if (verbose >= 2)
      msg("found propagate gate %s", internal_xor->get_var_name());

    Gate *g_0 = 0, *g_1 = 0;

    if (internal_xor->get_xor_gate() &&
        xor_left_child(internal_xor)->parents_size() != 2 &&
        xor_right_child(internal_xor)->parents_size() != 2 &&
        (i != 1 || !signed_mult || n->parents_size() == 1 || booth)) {
      Gate * internal_and = derive_ha_and_gate(internal_xor);
      internal_and->mark_prop_gen_gate();
      if (verbose >= 2)
        msg("found generate gate %s", internal_and->get_var_name());

      aiger_and * par = is_model_and(internal_and->get_var_num());
      g_0 = gate(par->rhs0);
      g_1 = gate(par->rhs1);
      g_0->mark_fsa_inp();
      g_1->mark_fsa_inp();
    } else if (booth) {
      internal_xor->mark_fsa_inp();

      if (verbose >= 3)  msg("pushed xor %s", internal_xor->get_var_name());
    }

    outputs.push_back(n);
    if (i != 1 || n->parents_size() == 1) {
      if (l->get_xor_gate()) push_to_cins(r);
      else push_to_cins(l);
    } else  {
      Gate * c = gate(slit(0));
      if (c->parents_size() > 1) {
         push_to_cins(c);
         outputs.push_back(c);
      } else if (booth && (g_0->get_xor_gate() || g_1->get_xor_gate())) {
        // bp-ba-csv
        Gate * not_xor_cin = g_0->get_xor_gate() ? g_1 : g_0;
        push_to_cins(not_xor_cin);
      }
    }
  }
  return 1;
}

/*------------------------------------------------------------------------*/
/**
    Follow all paths from the gate n and check that we stop at
    the identified inputs and carry-in of the final stage adder.
    All gates that are seen on the way are marked to belong to the final stage
    adder.

    @param n  Gate* pointing to root gate, from which we start the checks

    @return True if all checks succeeded
*/
static bool follow_path_and_mark_gates(Gate * n) {
  if (n->get_input() && !n->get_fsa_inp()) return 0;

  if (n->get_visited()) return 1;
  n->mark_visited();

  if(!n->get_fsa()) n->mark_fsa();

  if (n == carry_in) return 1;
  if (n->get_fsa_inp()) return 1;


  aiger_and * and1 = is_model_and(n->get_var_num());
  Gate * l = gate(and1->rhs0);
  if (!follow_path_and_mark_gates(l)) return 0;

  Gate * r = gate(and1->rhs1);
  if (!follow_path_and_mark_gates(r)) return 0;

  return 1;
}

/*------------------------------------------------------------------------*/
/**
    Calls follow_path_and_mark_gates for all identified output gates of
    the final stage adder.

    @return True if all checks succeeded
*/
static bool follow_all_output_paths_and_mark_gates() {
  msg("checking last stage adder");
  for (auto it = outputs.begin(); it != outputs.end(); ++it) {
    Gate * n = *it;
    if (verbose >= 3)  msg("follow path starting with %s", n->get_var_name());
    if (!follow_path_and_mark_gates(n)) return 0;
  }
  return 1;
}

/*------------------------------------------------------------------------*/
static void clear_all_fsa() {
  for (unsigned i = 0; i < M-1; i++) {
    Gate * n = gates[i];
    n->mark_fsa(0);
  }
}
/*--------------------------------------------------------------------------*/

bool identify_final_stage_adder() {
  if (!all_outputs_are_xor()) {
    msg("no gp adder detected - not all outputs are XORs");
    return 0;
  }
  if (!slice_two_needs_carry_in_slice_zero()) {
    msg("no gp adder detected - carry in slice 0 not found");
    return 0;
  }
  identify_carry_out();
  if (!identify_propagate_and_generate_gates()) {
    msg("no gp adder detected - propagate and generate gates not found");
    clear_all_fsa();
    return 0;
  }
  if (!follow_all_output_paths_and_mark_gates()) {
    msg("no gp adder detected - no clear boundaries");
    clear_all_fsa();
    return 0;
  }
  return 1;
}
/*----------------------------------------------------------------------------*/
