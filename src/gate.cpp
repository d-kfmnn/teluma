/*------------------------------------------------------------------------*/
/*! \file gate.cpp
    \brief contains the class Gate and further functions to
    organize the gate structure, such as initializing the gate constraints

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#include <string>
#include <list>

#include "gate.h"
/*------------------------------------------------------------------------*/
// Global variables
bool xor_chain = 0;
bool booth = 0;
bool signed_mult = 0;
/*------------------------------------------------------------------------*/

Gate::Gate(int n_, std::string name_, int level_, bool input_, bool output_):
  v(new Var(name_, level_, n_)), input(input_), output(output_)  {
    std::string negname = name_;
    negname.insert(1,1,'_');
    Var * d = new Var (negname, level_+1, n_, 1);
    v->set_dual_var(d);
    d->set_dual_var(v);
}

/*------------------------------------------------------------------------*/
bool Gate::orig() const {
  return ancestors.empty();
}

/*------------------------------------------------------------------------*/

Gate::~Gate() {
  delete(v->get_dual());
  delete(v);
  delete(co_factor);
  if (gate_constraint) delete(gate_constraint);
  for (std::map<Gate*, Polynomial*>::const_iterator it=ancestors.begin();
      it != ancestors.end(); ++it) {
    delete(it->second);
  }
}

/*------------------------------------------------------------------------*/

bool Gate::is_in_parents(const Gate * n) const {
  for (auto it=parents_begin();
      it != parents_end(); ++it) {
    Gate * parents = *it;
    if (parents == n) return 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

bool Gate::is_child(const Gate * n) const {
  for (auto it=children_begin();
      it != children_end(); ++it) {
    Gate * child = *it;
    if (child == n) return 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/
Polynomial * Gate::get_gate_constraint() const {
  if (!gate_constraint && !elim) {
    // output aig are 0, -1, ...-NN+2
    if (output) init_gate_constraint(-1*get_var_num()+M-1);
    // gates are numbered 2,4,6,8,..
    else
      init_gate_constraint(get_var_num()/2-1);
  }
  return gate_constraint;
}

Gate ** gates;
unsigned num_gates;

/*------------------------------------------------------------------------*/

Gate * gate(unsigned lit) {
  assert(lit < 2*M);
  return gates[lit/2-1];
}

/*------------------------------------------------------------------------*/

void allocate_gates(bool assert) {
  unsigned aiger;
  num_gates = M + NN - 1;

  msg("allocating %i gates", num_gates);
  gates = new Gate*[num_gates];

  if (!gates) die("failed to allocate gates");
  int level = 0;

  // inputs a
  for (unsigned i = a0; i <= al; i+=ainc) {
    aiger = 2*(i+1);
    if (assert) assert(is_model_input(aiger));

    std::string name = "a" + std::to_string((i-a0)/ainc);
    gates[i] = new Gate(aiger, name, level+=2, 1);
  }

  // inputs b
  for (unsigned i = b0; i <= bl; i+=binc) {
    aiger = 2*(i+1);
    if (assert) assert(is_model_input(aiger));

    std::string name = "b" + std::to_string((i-b0)/binc);
    gates[i] = new Gate(aiger, name, level+=2, 1);
  }

  // internal gates
  for (unsigned i = NN; i < M-1; i++) {
    aiger = 2*(i+1);
    if (assert) assert(is_model_and(aiger));

    std::string name = "l" + std::to_string(aiger);
    gates[i] = new Gate(aiger, name, level+=2);
  }

  // output s
  for (unsigned i = M-1; i < num_gates; i++) {
    aiger = i-M+1;

    std::string name = "s" + std::to_string(aiger);
    gates[i] = new Gate(M-i-1, name, level+=2, 0, 1);
    gates[i]->set_slice(aiger);
  }
}

/*------------------------------------------------------------------------*/

void mark_aig_outputs() {
  for (unsigned i = 0; i < NN; i++) {
    unsigned lit = slit(i);
    Gate * n = gate(lit);
    n->mark_aig_output();
  }
}

/*------------------------------------------------------------------------*/

Gate * derive_ha_and_gate(const Gate *n) {
  Gate * ll = xor_left_child(n);
  Gate * rr = xor_right_child(n);
  for (auto it_l=ll->parents_begin();
       it_l != ll->parents_end(); ++it_l) {
    Gate * ll_parent = *it_l;
    if (ll_parent -> get_xor_gate()) continue;

    aiger_and * and1 = is_model_and(ll_parent->get_var_num());
    Gate * c1 = gate(and1->rhs0);
    Gate * c2 = gate(and1->rhs1);

    if (c1 == ll && c2 == rr) return ll_parent;
    if (c1 == rr && c2 == ll) return ll_parent;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

void set_xor() {
  int found_xor = 0;
  for (unsigned i = 0; i < M; i++) {
    Gate * n = gates[i];
    if (n->get_input() > 0) continue;
    if (n->get_xor_gate() > 0) continue;

    aiger_and * and1 = is_model_and(n->get_var_num());
    if (!and1) continue;
    unsigned l = and1->rhs0, r = and1->rhs1;
    if (!aiger_sign(l)) continue;
    if (!aiger_sign(r)) continue;
    if (l == r || l == aiger_not(r)) continue;
    l = aiger_strip(l);
    r = aiger_strip(r);
    aiger_and * land = is_model_and(l);
    if (!land) continue;
    aiger_and * rand = is_model_and(r);
    if (!rand) continue;

    unsigned ll = land->rhs0, lr = land->rhs1;
    unsigned rl = rand->rhs0, rr = rand->rhs1;
    if ((ll == aiger_not(rl) && lr == aiger_not(rr)) ||
       (ll == aiger_not(rr) && lr == aiger_not(rl))) {
      gate(l)->set_xor_gate(2);
      gate(r)->set_xor_gate(2);
      n->set_xor_gate(1);
      found_xor++;
      if (verbose >= 4) msg("xor-gate %s", n->get_var_name());
    }
  }
  if (verbose >= 1) msg("found %i xor-gates", found_xor);
}

/*------------------------------------------------------------------------*/

bool upper_half_xor_output() {
  for (unsigned i = num_gates-2; i >= M+NN/2-1; i--) {
    Gate * n = gates[i]->children_front();
    if (!n->get_xor_gate()) return 0;
  }
  return 1;
}

/*------------------------------------------------------------------------*/

Gate * xor_left_child(const Gate * n) {
  if (!n->get_xor_gate() ) return 0;

  aiger_and * and1 = is_model_and(n->get_var_num());
  if (!and1) return 0;
  unsigned l = and1->rhs0;
  if (!aiger_sign(l)) return 0;
  l = aiger_strip(l);

  aiger_and * land = is_model_and(l);
  if (!land) return 0;

  unsigned ll = land->rhs0;
  return gate(ll);
}

/*------------------------------------------------------------------------*/

Gate * xor_right_child(const Gate * n) {
  if (!n->get_xor_gate() ) return 0;

  aiger_and * and1 = is_model_and(n->get_var_num());
  if (!and1) return 0;
  unsigned l = and1->rhs0;
  if (!aiger_sign(l)) return 0;
  l = aiger_strip(l);

  aiger_and * land = is_model_and(l);
  if (!land) return 0;

  unsigned lr = land->rhs1;
  return gate(lr);
}

/*------------------------------------------------------------------------*/

void mark_xor_chain_in_last_slice() {
  msg("marking xor chain gates");
  int counter = 0;

  Gate * out = gates[num_gates-1];
  assert(out->children_size() == 1);
  Gate * child = out->children_front();

  std::queue<Gate*> downwards_queue;
  if (child->get_xor_gate() == 1) downwards_queue.push(child);

  while (!downwards_queue.empty()) {
    Gate * n = downwards_queue.front();
    downwards_queue.pop();

    aiger_and * and1 = is_model_and(n->get_var_num());
    unsigned l = and1->rhs0;
    aiger_and * land = is_model_and(l);
    unsigned ll = land->rhs0, lr = land->rhs1;
    Gate * ll_gate = gate(ll);
    Gate * lr_gate = gate(lr);

    if (ll_gate->get_xor_gate()) downwards_queue.push(ll_gate);
    if (lr_gate->get_xor_gate()) downwards_queue.push(lr_gate);

    n->mark_xor_chain();
    if (verbose >= 4) msg("xor-chain %s", n->get_var_name());
    counter++;
  }
  if (verbose >= 1) msg("marked %i xor gates in last slice", counter);
  if (counter) xor_chain = 1;
}

/*------------------------------------------------------------------------*/

void set_parents_and_children(bool set_children) {
  unsigned pp = 0;

  for (unsigned i = NN; i < M; i++) {
    Gate * n = gates[i];
    assert(!n->get_input());

    aiger_and * and1 = is_model_and(n->get_var_num());

    if (!and1) continue;
    unsigned l = and1->rhs0, r = and1->rhs1;
    Gate * l_gate = gate(l), *r_gate = gate(r);

    if (set_children) {
      n->children_push_back(l_gate);
      n->children_push_back(r_gate);
    }

    n->set_level(l_gate->get_level() > r_gate->get_level() ?
                 l_gate->get_level()+1 : r_gate->get_level()+1);

    l_gate->parents_push_back(n);
    r_gate->parents_push_back(n);

    if (l_gate->get_input() && r_gate->get_input()
          && !aiger_sign(l) && !aiger_sign(r)) {
      n->mark_pp();
      pp++;
      if (verbose >= 4) msg("partial product %s", n->get_var_name());
    }
  }

  // set children for extra outputs
  for (unsigned i = 0; i < NN; i++) {
    Gate * n = gates[i+M-1];
    assert(n->get_output());
    Gate * model_output_gate = gate(slit(i));
    if (set_children) n->children_push_back(model_output_gate);
    model_output_gate->parents_push_back(n);
  }

  if (verbose >= 1) msg("found %i partial products", pp);
  if (pp == NN*NN/4) {
    msg("assuming simple pp generator");
  } else {
    booth = 1;
    msg("assuming booth recoding");
  }
}

/*------------------------------------------------------------------------*/

bool parents_are_in_equal_or_larger_slice(const Gate * n, int i) {
  for (auto it_n = n->parents_begin();
       it_n != n->parents_end(); ++it_n) {
    Gate * n_parent = *it_n;
    if (n_parent->get_slice() != -1 && n_parent->get_slice() < i) return 0;
  }
  return 1;
}

/*------------------------------------------------------------------------*/
Polynomial * gen_dual_constraint(const Var * v) {
  const Var * d = v->get_dual();
  Term * t = new_term(d, 0);
  Term * t1 = new_term(v, 0);
  Monomial * m, * m1, * m2;

  m = new Monomial(minus_one, t);
  m1 = new Monomial(minus_one, t1);
  m2 = new Monomial(one, 0);

  Polynomial * p = new Polynomial();
  p->mon_push_back(m);
  p->mon_push_back(m1);
  p->mon_push_back(m2);
  p->set_idx((v->get_num())-2*NN+1);

  return p;
}


/*------------------------------------------------------------------------*/

static Polynomial * negative_poly(const Var * v) {
  Polynomial * p = new Polynomial();

  Term * t1 = new_term(v, 0);
  Monomial * m1 = new Monomial(minus_one, t1);
  p->mon_push_back(m1);

  Monomial * m2 = new Monomial(one, 0);
  p->mon_push_back(m2);

  return p;
}

/**
    Defines the polynomial 'v'

    @param v Var*

    @return Polynomial*
*/
static Polynomial * positive_poly(const Var * v) {
  Term * t = new_term(v, 0);
  Monomial * m = new Monomial(one, t);
  Polynomial * p = new Polynomial();
  p->mon_push_back(m);

  return p;
}

/*------------------------------------------------------------------------*/
Polynomial * gen_gate_constraint(unsigned i) {
  assert(i >= NN && i < M + NN - 1);
  Polynomial * p = new Polynomial();
  // gate constraint
  if (i < M-1) {
    Gate * n = gates[i];
    assert(!n->get_input());

    aiger_and * and1 = is_model_and(n->get_var_num());
    assert(and1);

    unsigned l = and1->rhs0, r = and1->rhs1;
    Gate * l_gate = gate(l), *r_gate = gate(r);

    const Var * v = n->get_var();

    Term * t1 = new_term(v, 0);
    Monomial * m1 = new Monomial(minus_one, t1);

    const Var * v1 = l_gate->get_var();
    const Var * v2 = r_gate->get_var();
    const Var * d1 = v1->get_dual();
    const Var * d2 = v2->get_dual();
    unsigned sign1 = aiger_sign(and1->rhs0);
    unsigned sign2 = aiger_sign(and1->rhs1);

    Polynomial * p1;
    Polynomial * p2;

    bool n_is_fsa_but_no_xor = n->get_fsa() && !n->get_xor_gate();

    if (sign1 && !l_gate->get_input() && n_is_fsa_but_no_xor) p1 = positive_poly(d1);
    else if (sign1) p1 = negative_poly(v1);
    else p1 = positive_poly(v1);

    if (sign2 && !r_gate->get_input() && n_is_fsa_but_no_xor) p2 = positive_poly(d2);
    else if (sign2) p2 = negative_poly(v2);
    else p2 = positive_poly(v2);

    Polynomial * p_tl = multiply_poly(p1, p2);
    p->mon_push_back(m1);

    link_poly(p, p_tl);

    delete(p_tl);

    delete(p1);
    delete(p2);
  } else {  // output
    Gate * n = gates[i];
    assert(n->get_output());

    Gate * model_output_gate = n->children_front();
    if (!model_output_gate) die("init gate constraint not working");
    const Var * v = n->get_var();
    Term * t1 = new_term(v, 0);
    Monomial * m1 = new Monomial(minus_one, t1);

    Polynomial * p_tl;
    if (aiger_sign(slit(i-M+1)))
      p_tl = positive_poly(model_output_gate->get_var()->get_dual());
    else
      p_tl = positive_poly(model_output_gate->get_var());
    p->mon_push_back(m1);

    link_poly(p, p_tl);

    delete(p_tl);
  }
  p->set_idx(2*(1+i-NN));
  return p;
}


void init_gate_constraint(unsigned i) {
  assert(i >= NN && i < M + NN - 1);
  Polynomial * p = gen_gate_constraint(i);
  Gate * n = gates[i];
  n->set_gate_constraint(p);
}


void init_gate_constraints() {
  for (unsigned i = NN; i < M-1; i++) {
    init_gate_constraint(i);
  }

  for (unsigned i = 0; i < NN; i++) {
    init_gate_constraint(i+M-1);
  }
}

/*------------------------------------------------------------------------*/

void delete_gates() {
  for (unsigned i = 0; i < num_gates; i++) {
    delete(gates[i]);
  }
  delete[] gates;
}
