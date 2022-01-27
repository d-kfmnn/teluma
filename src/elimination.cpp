/*------------------------------------------------------------------------*/
/*! \file elimination.cpp
    \brief contains functions used in the polynomial solver

  This file contains all functions used for preprocessing the Gröbner basis
  and for reducing the specification by the slices.

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#include <algorithm>
#include <deque>
#include <list>

#include "elimination.h"
/*------------------------------------------------------------------------*/
// Global variables
int proof = 0;

/*------------------------------------------------------------------------*/
// Local variables

// / used to collect the factors of each slice for PAC proofs
static std::vector<Polynomial*> factors_per_slice;

// / used to collect the cofactors of each slice for PAC proofs
static std::vector<const Polynomial*> co_factors;

// / used to collect the cofactors of each slice for PAC proofs
static std::vector<int> factor_indices;

// / used to collect the cofactors of each slice spec for PAC proofs
static std::vector<int> spec_indices;

// / used to collect the specification of each slice for PAC proofs
static std::vector<Polynomial*> spec_of_slice;

/*-------------------------------------------------------------------------*/
Polynomial * add_up_factors(FILE * file, bool print) {
  Polynomial * p = factors_per_slice.back();
  factors_per_slice.pop_back();

  while (!factors_per_slice.empty()) {
    Polynomial * q = factors_per_slice.back();
    factors_per_slice.pop_back();

    Polynomial * add = add_poly(p, q);
    if (print) {
      print_pac_add_rule(file, p, q, add);
      //fprintf(stdout,"mod in ad up fac\n");
      add = mod_poly(add, 1, file);
      print_pac_del_rule(file, p);
      print_pac_del_rule(file, q);
    }
    delete(p);
    delete(q);
    p = add;
  }

  return p;
}



/*------------------------------------------------------------------------*/
struct {
    bool operator()(Monomial * a, Monomial * b) const {
      return a->get_size() > b->get_size();
     }
} cmpmonSize;

static const Var * compare_terms_for_one_dual_difference(Term * t1, Term * t2){
  if (t1->get_size() != t2->get_size()) return 0;
  if ((t1->get_dual_count()^t2->get_dual_count()) != 1) return 0;
  const Var * v = 0;

  while (t1 && t2 && t1->get_var() == t2->get_var()){
    t1 = t1->get_rest();
    t2 = t2->get_rest();
  }
  if (t1->get_var() == t2->get_var()->get_dual()){
      v = t1->get_var();
      t1 = t1->get_rest();
      t2 = t2->get_rest();
  } else {
    return 0;
  }

  if(t1 != t2) return 0;


  return v;
}


static Polynomial * f_and_l_is_one(Polynomial * p, bool proof_print, FILE * file) {
  bool pac_print = proof_print &(proof == 1 || proof == 2);
  if(p->get_size() <= 2) return p->copy();
   //fprintf(stdout,"start f_and_l\n");

  Polynomial * tmp = p->copy();
  Polynomial * tmp2 = tmp->copy();
  Monomial * m1, * m2;
  Term * t1, * t2;
  bool change = 1;
  std::vector<Monomial *> tmp_stack;

  mpz_t exp;
  mpz_init(exp);
  mpz_pow_ui(exp, base, NN);
  mpz_t exp_half;
  mpz_init(exp_half);
  mpz_pow_ui(exp_half, base, NN-1);
  mpz_t mod1;
  mpz_init(mod1);
  mpz_t mod2;
  mpz_init(mod2);

  std::deque<Monomial*> largest;
  size_t max_size;
  int counter = 0;

  while(change){
    change = 0;
    counter++;
    std::deque<Monomial*> mon = tmp->get_mon();
    std::sort(mon.begin(), mon.end(), cmpmonSize);
    max_size = mon[0]->get_size();

    for(size_t i = 0; i < mon.size(); i++){
      m1 = mon[i];

      bool match_found = 0;

      for(auto it2 = mon.begin()+i+1; it2 != mon.end(); ++it2) {

        m2 = *it2;
        if (m1->get_size() != m2->get_size()) break;

        t1 = m1->get_term(); t2 = m2->get_term();
        const Var * v =  compare_terms_for_one_dual_difference(t1, t2);
        if(!v) continue;
//from here
        if (mpz_cmp(m1->coeff, m2->coeff) == 0) {
          while (t1){
              if(t1->get_var() != v) add_to_vstack(t1->get_var());
              t1 = t1->get_rest();
          }

          match_found = 1;
          change = 1;
          Term * t = build_term_from_stack();

          Monomial * m_tmp;
          if(t) m_tmp = new Monomial(m1->coeff, t);
          else  m_tmp = new Monomial(m1->coeff, 0);

          tmp_stack.push_back(m_tmp);
          mon.erase(it2);

          if(pac_print){

            Polynomial * flip = gen_dual_constraint(v);
            Polynomial * t_poly = new Polynomial();
            t_poly->mon_push_back(new Monomial(m1->coeff, t));
            Polynomial * mul = multiply_poly(flip, t_poly);
            Polynomial * add = add_poly(mul, tmp2);
            if(proof == 1){
              print_pac_mul_rule(file, flip, t_poly, mul);

              print_pac_add_rule(file, mul, tmp2, add);
              print_pac_del_rule(file, mul);
              print_pac_del_rule(file, tmp2);

            } else if (proof == 2){
              print_pac_combi_rule(file, flip, t_poly, tmp2, 0, add);
            }

            delete(flip);
            delete(mul);
            delete(t_poly);
            delete(tmp2);
            tmp2 = add;

          }

          break;
        }
// to here could we get rid of
        else {
          mpz_mod(mod1, m1->coeff, exp);
          mpz_mod(mod2, m2->coeff, exp);
          if (mpz_cmp(mod1, mod2) == 0) {

            while (t1){
                if(t1->get_var() != v) add_to_vstack(t1->get_var());
                t1 = t1->get_rest();

            }

            match_found = 1;
            change = 1;
            Term * t = build_term_from_stack();

            Monomial * m_tmp;
            if(mpz_cmp(mod1, exp_half) > 0) mpz_sub(mod1, mod1, exp);
            if(t) m_tmp = new Monomial(mod1, t);
            else  m_tmp = new Monomial(mod1, 0);

            tmp_stack.push_back(m_tmp);
            mon.erase(it2);
            if(pac_print){
              //fprintf(stdout,"second\n");
              Polynomial * flip = gen_dual_constraint(v);
              Polynomial * t_poly = new Polynomial();
              t_poly->mon_push_back(new Monomial(mod1, t));
              Polynomial * mul = multiply_poly(flip, t_poly);
              Polynomial * add = add_poly(mul, tmp2);
              if(proof == 1){
                print_pac_mul_rule(file, flip, t_poly, mul);

                print_pac_add_rule(file, mul, tmp2, add);
                print_pac_del_rule(file, mul);
              } else if (proof ==2){
                print_pac_combi_rule(file, flip, t_poly, tmp2, 0, add);
              }
              print_pac_del_rule(file, tmp2);
              delete(flip);
              delete(mul);
              delete(t_poly);
              delete(tmp2);
              tmp2 = add;
              //fprintf(stdout,"mod in fl\n");
              tmp2 = mod_poly(tmp2, 1, file);

            }

            break;
          }
        }
      }
      if(!match_found && m1->get_size() == max_size) largest.push_back(m1->copy());
      else if(!match_found) tmp_stack.push_back(m1->copy());
    }
    delete(tmp);

    for(auto it = tmp_stack.begin(); it != tmp_stack.end(); ++it){
      push_mstack_end(*it);
    }
    tmp_stack = std::vector<Monomial*>();
    tmp = build_poly(1);
  }

  if(!largest.empty()){
    for(size_t i = 0; i < largest.size(); i++){
      push_mstack_end(largest[i]);
    }
    Polynomial * largest = build_poly(1);
    Polynomial * res = add_poly(tmp, largest);
    delete(largest);
    delete(tmp);
    tmp = res;
  }


  if(proof && counter == 1) tmp->set_idx(p->get_idx());
//  tmp->print(file);
//  tmp2->print(file);

  mpz_clear(exp); mpz_clear(mod1); mpz_clear(mod2); mpz_clear(exp_half);
tmp->set_idx(tmp2->get_idx());
  //fprintf(stdout,"fl done\n");
  if(pac_print) return tmp2;
  else return tmp;

}
/**
    Merges computed factors of a slice of the same level.
    Prints PAC rules for the process. Used only when proof == 1 or proof == 2.

    @param file output file for PAC rules
    @param container vector containing the factors, ordered by level

    @return vector of polynomials such that each polynomial has a unique level
*/
static std::vector<Polynomial*> add_and_merge_factors( FILE * file,
    Polynomial * add_p, std::vector<Polynomial*> container, bool print) {
  if (container.empty()) {
    container.push_back(add_p);
    return container;
  }

  Polynomial * p = add_p;
  Polynomial * q = container.back();

  if (p->get_level() != q->get_level()) {
    container.push_back(add_p);
  } else {
    Polynomial * add = add_poly(p, q);

    if (print)  {
      print_pac_add_rule(file, p, q, add);
      //fprintf(stdout,"mod in ad and merge\n");
      add = mod_poly(add, 1, file);
      if (add->contains_dual_var()) {
         Polynomial * tmp = f_and_l_is_one(add, 1, file);
         delete(add);
         add = tmp;
         //tmp->print(file);
         //fprintf(stdout,"mod poly in add and merge\n");
         add = mod_poly(add, 1, file);
      }

      print_pac_del_rule(file, p);
      print_pac_del_rule(file, q);
    }
    add->set_level(p->get_level()+1);
    delete(p);
    delete(q);
    container.pop_back();
    container = add_and_merge_factors(file, add, container, print);
  }
  return container;
}

/*------------------------------------------------------------------------*/

Polynomial * add_up_spec_of_slice(FILE * file, bool print) {
  Polynomial * p = spec_of_slice.back();
  spec_of_slice.pop_back();
  //fprintf(stdout,"add_up_spec_of_slice\n");

  while (!spec_of_slice.empty()) {
    Polynomial * q = spec_of_slice.back();
    spec_of_slice.pop_back();

    Polynomial * add = add_poly(p, q);
    if (print) {
      print_pac_add_rule(file, p, q, add);
      //fprintf(stdout,"mod in ad spe1\n");
      add = mod_poly(add, 1, file);
      if (add->contains_dual_var()) {
         Polynomial * tmp = f_and_l_is_one(add, 1, file);
         delete(add);
         add = tmp;
         //fprintf(stdout,"mod in ad spe\n");
         add = mod_poly(add, 1, file);
      }
      print_pac_del_rule(file, p);
      print_pac_del_rule(file, q);
    }

    delete(p);
    delete(q);
    p = add;
  }
  return p;
}

/*------------------------------------------------------------------------*/

const Polynomial * cofac_tmp, * base_tmp, * mul_tmp;
/*------------------------------------------------------------------------*/
const Var * term_contains_var_and_dual(Term *t){
  while(t && t->get_rest()){
    if(t->get_var()->get_dual() == t->get_rest()->get_var()) return t->get_var();
    t = t->get_rest();
  }
  return 0;
}


Polynomial * multiply_poly_dual_proof(FILE * file, const Polynomial * p1, Polynomial * p2, bool update){
  if(!proof) return multiply_poly(p1, p2);

  Polynomial * tmp = multiply_poly(p1, p2, 0);
  print_pac_mul_rule(file, p2, p1, tmp);

  bool change = 1;
  while(change) {
    change = 0;
    const Var * v = 0;
    for(auto it = tmp->mon_begin(); it != tmp->mon_end(); ++it){
      Monomial * m = *it;
      Term * t = m->get_term();
      if(t){
        v = term_contains_var_and_dual(t);
        if (v){
          Term * t0 = remainder(t, v);
          Polynomial * flip = gen_dual_constraint(v);
          Polynomial * mul = new Polynomial();
          mul->mon_push_back(new Monomial(m->coeff, t0));
          Polynomial * fac = multiply_poly(flip, mul,0);
          Polynomial * add = add_poly(tmp, fac);
          if(proof == 1){
            print_pac_mul_rule(file, flip, mul, fac);
            print_pac_add_rule(file, tmp, fac, add);
          } else if (proof == 2 && update){
            co_factors.push_back(mul->copy());
            factor_indices.push_back(flip->get_idx());
          } else if (proof == 2){
            print_pac_combi_rule(file, flip, mul, tmp, 0, add);
            print_pac_del_rule(file, tmp);
          }
          delete(flip);
          delete(mul);
          delete(fac);
          delete(tmp);
          tmp = add;
          change = 1;
          break;
        }
      }
    }
  }

  return tmp;

}

/*------------------------------------------------------------------------*/
Polynomial * reduce_by_one_poly(
    const Polynomial * p1, Polynomial * p2, FILE * file, bool update) {

  if(!p2) return p1->copy();

  const Polynomial * negfactor = divide_by_term(p1, p2->get_lt());
  if (negfactor->is_constant_zero_poly()) {
    delete(negfactor);
    return p1->copy();
  }

  Polynomial * mult   = multiply_poly_dual_proof(file, negfactor, p2, update);
  Polynomial * rem    = add_poly(p1, mult);

  if (!proof) {
    delete(mult);
    delete(negfactor);
  } else if (proof == 1) {
    assert(file);

    if (mult && update) {
      factors_per_slice = add_and_merge_factors(file, mult, factors_per_slice, 1);

    } else if (mult) {
      print_pac_add_rule(file, p1, mult, rem);
    } else {
      delete(mult);
    }

    delete(negfactor);
  } else if (proof == 2) {
    assert(file);
    if (mult && update) {
      co_factors.push_back(negfactor);
      factor_indices.push_back(p2->get_idx());
      factors_per_slice = add_and_merge_factors(file, mult, factors_per_slice, 0);
    } else if (mult) {
      print_pac_add_rule(file, p1, mult, rem);
    } else {
      delete(mult);
      delete(negfactor);
    }
  }

  return rem;
}

/*------------------------------------------------------------------------*/
static Polynomial * reduce_by_one_gate(const Polynomial * p1, Gate * n, FILE * file) {

  Polynomial * p2 = n->get_gate_constraint();
  Polynomial * rem;

  if(p1->contains_dual_var()){
    Polynomial * flip = gen_dual_constraint(n->get_var());
    //fprintf(stdout,"unflip in reduce gate\n");
    Polynomial * rem1 = reduce_by_one_poly(p1, flip, file);
    delete(flip);
    //fprintf(stdout,"reduce gate\n");
    rem = reduce_by_one_poly(rem1, p2, file);
    //fprintf(stdout,"reduce gate done\n");
    delete(rem1);

    Polynomial * rem2 = f_and_l_is_one(rem, 0, file);
    delete(rem);
    return rem2;

  } else {
    rem = reduce_by_one_poly(p1, p2, file);
    return rem;
  }
}
/*------------------------------------------------------------------------*/
static Polynomial * unflip_inputs(
    const Polynomial * p1, FILE * file) {

  Polynomial * p = p1->copy();
  bool change = 1;

  while (!p->is_constant_zero_poly() && change){
    change = 0;
    Term * lt = p->get_lt();

    while(lt) {
      if(lt->get_var()->is_dual()) {
        Polynomial * flip = gen_dual_constraint(lt->get_var()->get_dual());
        Polynomial * rem1 = reduce_by_one_poly(p, flip, file);
        delete(flip); delete(p);
        //fprintf(stdout,"mod in unflip\n");
        rem1 = mod_poly(rem1, 0, file);
        p = rem1;
        change = 1;
        break;
      }
      lt = lt->get_rest();
    }
  }

  return p;
}
/*------------------------------------------------------------------------*/
void eliminate_by_one_gate(Gate * n1, Gate *n2, FILE * file, bool update) {
  Polynomial * tmp_p1 = n1->get_gate_constraint();
  Polynomial * flip = gen_dual_constraint(n2->get_var());
  Polynomial * p1 = reduce_by_one_poly(tmp_p1, flip, file, 0);

  Polynomial * p2 = n2->get_gate_constraint();
  const Polynomial * negfactor = divide_by_term(p1, p2->get_lt());


  if (negfactor->is_constant_zero_poly()) {
    delete(p1);
    delete(negfactor);
    delete(flip);
    return;
  }


  Polynomial * mult   = multiply_poly_dual_proof(file, negfactor, p2, update);
  Polynomial * rem    = add_poly(p1, mult);


  if (proof) {
    assert(file);

    print_pac_add_rule(file, p1, mult, rem);
    print_pac_del_rule(file, mult);
  }

  if(p1->contains_dual_var() || p2->contains_dual_var()) {
    Polynomial * rem2 = f_and_l_is_one(rem, 1, file);
    delete(rem);
    n1->set_gate_constraint(rem2);
  } else n1->set_gate_constraint(rem);

  delete(flip);
  delete(mult);
  delete(negfactor);
  delete(p1);
  delete(tmp_p1);
}

/*------------------------------------------------------------------------*/


void remove_internal_xor_gates(FILE * file) {

  msg("remove internal xor gates");
  int counter = 0;
  for (unsigned i = NN; i < M-1; i++) {
    Gate * n = gates[i];
    if (n->get_xor_gate() != 1) continue;
    if (n->get_elim()) continue;
    assert(n->children_size() == 2);

    Gate * l_gate = n->children_front();
    Gate * r_gate = n->children_back();
    if (l_gate->get_xor_gate() != 2) continue;
    if (r_gate->get_xor_gate() != 2) continue;
    assert(l_gate->children_size() == 2);
    assert(r_gate->children_size() == 2);
    Gate * ll_gate = l_gate->children_front();
    Gate * lr_gate = l_gate->children_back();

    // set xor children to ll and lr by overwriting l and r
    n->set_children_front(ll_gate);
    n->set_children_back(lr_gate);

    lr_gate->parents_push_back(n);
    ll_gate->parents_push_back(n);
    eliminate_by_one_gate(n, l_gate, file);

    if (l_gate->parents_size() == 1) {
      if (proof == 1 || proof == 2) {
        assert(file);
        print_pac_del_rule(file, l_gate->get_gate_constraint());
      }
      l_gate->mark_elim();
      delete(l_gate->get_gate_constraint());
      l_gate->set_gate_constraint(0);

      if (verbose >= 3) msg("removed %s", l_gate->get_var_name());
      counter++;

      ll_gate->parents_remove(l_gate);
      lr_gate->parents_remove(l_gate);
    }

    eliminate_by_one_gate(n, r_gate, file);

    if (r_gate->parents_size() == 1) {
      if (proof == 1 || proof == 2) {
        assert(file);
        print_pac_del_rule(file, r_gate->get_gate_constraint());
      }

      r_gate->mark_elim();
      delete(r_gate->get_gate_constraint());
      r_gate->set_gate_constraint(0);

      if (verbose >= 3) msg("removed %s", r_gate->get_var_name());
      counter++;

      ll_gate->parents_remove(r_gate);
      lr_gate->parents_remove(r_gate);
    }
  }

  if (verbose >= 1) msg("removed %i internal xor gates", counter);
}

/*------------------------------------------------------------------------*/

void remove_single_occs_gates(FILE * file) {

  msg("remove single occurence gates");
  int counter = 0;
  for (unsigned i = M-2; i >= NN; i--){
    Gate * n = gates[i];

    if (n->get_elim()) continue;
    if (n->get_fsa()) continue;
    if (n->parents_size() > 1) continue;

    Gate * parent = n->parents_front();
    if (parent->get_output()) continue;

    if (!n->get_xor_gate() && parent->get_xor_gate() == 1) continue;
    if (n->get_xor_chain()) continue;

    eliminate_by_one_gate(parent, n, file, 0);
    parent->children_remove(n);

    for (auto it = n->children_begin(); it != n->children_end(); ++it) {
      Gate * n_child = *it;
      if (!parent->is_child(n_child)) parent->children_push_front(n_child);

      n_child->parents_remove(n);
      n_child->parents_push_back(parent);
    }

    if (proof == 1 || proof == 2) {
      assert(file);
      print_pac_del_rule(file, n->get_gate_constraint());
    }

    n->mark_elim();
    if(n->get_gate_constraint()) delete(n->get_gate_constraint());
    n->set_gate_constraint(0);

    if (verbose >= 3)
    msg("removed %s in %s", n->get_var_name(), parent->get_var_name());
    //  parent->get_gate_constraint()->print(stdout);

    counter++;
  }

  if (verbose >= 1) msg("removed %i single occurence gates", counter);

}

/*------------------------------------------------------------------------*/
void remove_nodes_which_occurr_with_their_children(FILE * file) {

  msg("remove nodes which occur with their parents");
  int counter = 0;
  for (unsigned i = M-2; i >= NN; i--){
    Gate * n = gates[i];

    if (n->get_elim()) continue;
    if (n->get_pp()) continue;
    if (n->get_fsa()) continue;
    if (n->get_gate_constraint()->get_size() != 2) continue;
    if (n->parents_size() != 2) continue; //we only need that case for -cn-

    Gate * p1 = n->parents_front();
    if (p1->get_elim()) continue;

    Gate * p2 = n->parents_back();
    if (p2->get_elim()) continue;
    if(p1->get_gate_constraint()->get_size() >
       p2->get_gate_constraint()->get_size())
      std::swap(p1,p2);

    auto it_c = (n->children_begin())++;
    while(it_c != n->children_end()){
      if(!p2->is_child(*it_c)) break;
      it_c++;
    }
    if(it_c != n->children_end()) continue;

    it_c = (p1->children_begin())++;
    while(it_c != p1->children_end()){
      if(!p2->is_child(*it_c)) break;
      it_c++;
    }
    if(it_c != p1->children_end()) continue;

    for (auto it_p = n->parents_begin(); it_p != n->parents_end(); ++it_p) {
      Gate * n_parent = *it_p;
      eliminate_by_one_gate(n_parent, n, file);
      n_parent->children_remove(n);
    }

    if (proof == 1 || proof == 2) {
      assert(file);
      print_pac_del_rule(file, n->get_gate_constraint());
    }

    n->mark_elim();
    delete(n->get_gate_constraint());
    n->set_gate_constraint(0);

    counter++;
    //if (verbose >= 3)
      msg("removed %s", n->get_var_name());

  }
  if (verbose >= 1)
     msg("removed %i gates that occur with their children", counter);
}

/*------------------------------------------------------------------------*/

void remove_slice_minus_one_gates(FILE * file) {
  msg("remove gates that are not assigned to slices");
  int counter = 0;
  for (unsigned i = NN; i < M-1; i++) {
    Gate * n = gates[i];
    if (n->get_elim()) continue;
    if (n->get_slice() > -1) continue;
    assert(!n->get_input());

    for (auto it_c = n->children_begin();
        it_c != n->children_end(); ++it_c) {
      Gate * n_child = *it_c;
      n_child->parents_remove(n);
    }

    for (auto it_p = n->parents_begin();
        it_p != n->parents_end(); ++it_p) {
      Gate * n_parent = *it_p;
      eliminate_by_one_gate(n_parent, n, file);
      n_parent->children_remove(n);
    }

    if (proof == 1 || proof == 2) {
      assert(file);
      print_pac_del_rule(file, n->get_gate_constraint());
    }

    n->mark_elim();
    delete(n->get_gate_constraint());
    n->set_gate_constraint(0);

    counter++;
    if (verbose >= 3) msg("removed %s", n->get_var_name());
  }
  if (verbose >= 1)
    msg("removed %i gates that are not assigned to slices", counter);


}

/*------------------------------------------------------------------------*/



/*------------------------------------------------------------------------*/
void decomposing(FILE * file) {
  msg("eliminate single occs");
  int counter = 0;
  int begin = xor_chain ? NN-2 : NN-1;
  for (int i = begin; i >= 0; i--) {
    bool change = 1;
    while (change) {
      change = 0;
      for (auto it =slices[i].begin();
          it != slices[i].end(); ++it) {
        Gate * n = *it;
        if (n->get_elim()) continue;

        if (n->parents_size() == 1 && !n->get_carry_gate()) {
          Gate * parent = n->parents_front();

          eliminate_by_one_gate(parent, n, file);
          parent->children_remove(n);


          for (auto it=n->children_begin();
              it != n->children_end(); ++it) {
            Gate * n_child = *it;
            if (!parent->is_child(n_child))
              parent->children_push_back(n_child);

            n_child->parents_remove(n);

            if (!n_child->is_in_parents(parent))
              n_child->parents_push_back(parent);
          }
          if (proof == 1 || proof == 2) {
            assert(file);
            print_pac_del_rule(file, n->get_gate_constraint());
          }

          n->mark_elim();
          delete(n->get_gate_constraint());
          n->set_gate_constraint(0);

          counter++;

          ++it;
          slices[i].remove(n);
          change = 1;

          if (verbose >= 3)
            msg("decomposed %s", n->get_var_name());
        }
      }
    }
  }
  msg("decomposed %i variables", counter);
}

/*------------------------------------------------------------------------*/

void eliminate_booth_pattern(FILE * file) {
  msg("eliminate booth pattern");
  int counter = 0;
  for (unsigned i = NN; i < M-1; i++) {
    Gate * n = gates[i];
    if (!n->get_bo()) continue;
    if (n->get_elim()) continue;

    for (auto it_c=n->children_begin();
        it_c != n->children_end(); ++it_c) {
      Gate * n_child = *it_c;
      n_child->parents_remove(n);
    }

    for (auto it_p=n->parents_begin();
        it_p != n->parents_end(); ++it_p) {
      Gate * n_parent = *it_p;
      eliminate_by_one_gate(n_parent, n, file);
      n_parent->children_remove(n);
      for (auto it_c=n->children_begin();
          it_c != n->children_end(); ++it_c) {
        Gate * n_child = *it_c;
        n_parent->children_push_back(n_child);
        n_child->parents_push_back(n_parent);
      }
    }

    if (proof == 1 || proof == 2) {
      assert(file);
      print_pac_del_rule(file, n->get_gate_constraint());
    }

    n->mark_elim();
    delete(n->get_gate_constraint());
    n->set_gate_constraint(0);

    counter++;
    if (verbose >= 3) {
      msg("eliminated %s", n->get_var_name());
    }
  }
  msg("eliminated %i variables from booth pattern", counter);
}

/*------------------------------------------------------------------------*/

Polynomial * inc_spec_poly(unsigned i) {
  mpz_t coeff;
  mpz_init(coeff);

  mpz_pow_ui(coeff, base, i);
  if (i == NN-1 && signed_mult) mpz_neg(coeff, coeff);

  const Var * s = gates[i+M-1]->get_var();
  Term * t1 = new_term(s, 0);
  Monomial * m1 = new Monomial(coeff, t1);
  push_mstack_end(m1);

  mpz_neg(coeff, coeff);

  int min_start = std::min(NN/2-1, i);
  for (int j = min_start; j >= 0; j--) {
    if (mpz_sgn(coeff) == 1) mpz_neg(coeff, coeff);
    const Var * b = gates[b0+j*binc]->get_var();
    unsigned k = i - j;
    if (k > NN/2-1) break;
    if (k == NN/2-1 && signed_mult) mpz_neg(coeff, coeff);
    if (j == static_cast<int>(NN/2-1) && signed_mult) mpz_neg(coeff, coeff);

    const Var * a = gates[a0+k*ainc]->get_var();
    add_to_vstack(b);
    add_to_vstack(a);
    Term * t1 = build_term_from_stack();
    Monomial * m1 = new Monomial(coeff, t1);
    push_mstack_end(m1);
  }
  mpz_clear(coeff);

  Polynomial * res = build_poly();
  return res;
}

/*------------------------------------------------------------------------*/

Polynomial * mod_poly(const Polynomial *p1, bool print_rule, FILE * file) {
  bool pac_print = print_rule &(proof == 1 || proof == 2);
  int exp = NN;

  mpz_t coeff;
  mpz_init(coeff);

  for (std::deque<Monomial*>::const_iterator it=p1->mon_begin();
      it != p1->mon_end(); ++it) {
    Monomial * m = *it;

    mpz_tdiv_r_2exp(coeff, m->coeff, exp);
    if (mpz_sgn(coeff) != 0) {
      Monomial * tmp;
      if (m->get_term()) tmp =  new Monomial(coeff, m->get_term_copy());
      else
        tmp =  new Monomial(coeff, 0);
      push_mstack_end(tmp);
    }
  }
  mpz_clear(coeff);
  Polynomial * out = build_poly();
  out->set_idx(p1->get_idx());

  if (pac_print || proof == 3) {
    mpz_t quot;
    mpz_init(quot);
    for (std::deque<Monomial*>::const_iterator it = p1->mon_begin();
        it != p1->mon_end(); ++it) {
      Monomial * m = *it;
      if (pac_print || proof == 3) {
        mpz_tdiv_q_2exp(quot, m->coeff, exp);
        if (mpz_sgn(quot) != 0) {
          mpz_neg(quot, quot);
          Monomial * tmp;
          if (m->get_term()) tmp =  new Monomial(quot, m->get_term_copy());
          else
            tmp =  new Monomial(quot, 0);
          push_mstack_end(tmp);
        }
      }
    }
    mpz_clear(quot);
  }

  if (pac_print && !mstack_is_empty()) {
    assert(file);
    Polynomial * p = build_poly();
    Polynomial * mod = multiply_poly_with_constant(p, mod_coeff);
    print_pac_mod_rule(file,  p, mod);
    print_pac_add_rule(file,  p1, mod, out);

    delete(p);
    delete(mod);
  } else if (proof == 3 && !mstack_is_empty()) {
    Polynomial * p = build_poly();
    add_fac_mod(p);
    delete(p);
  }

  delete(p1);
  return out;
}

/*------------------------------------------------------------------------*/

void correct_pp_unsigned(const Polynomial * p, FILE * file) {
  for (std::deque<Monomial *>::const_iterator it=p->mon_begin();
      it != p->mon_end(); ++it) {
    Monomial * m = *it;

    if (mpz_sgn(m->coeff) == -1) {
      Term * t = m->get_term();
      if (!t) continue;
      if (t->get_var_num() <= 0) continue;
      if (!gate(t->get_var_num())->get_input()) continue;
      push_mstack_end(new Monomial(one, t->copy()));
    }
  }

  if (!mstack_is_empty()) {
    Polynomial * factor = build_poly();
    Polynomial * mod = multiply_poly_with_constant(factor, mod_coeff);
    print_pac_mod_rule(file,  factor, mod);
    Polynomial * add = add_poly(mod, p);
    print_pac_add_rule(file,  mod, p, add);
    delete(factor);
    delete(mod);
    delete(add);
  }
}

/*------------------------------------------------------------------------*/

void correct_pp_signed(const Polynomial * p, FILE * file) {
  mpz_t half_mod;
  mpz_init(half_mod);
  mpz_pow_ui(half_mod, base, NN-1);

  mpz_t half_mod_neg;
  mpz_init(half_mod_neg);
  mpz_neg(half_mod_neg, half_mod);

  for (std::deque<Monomial *>::const_iterator it=p->mon_begin();
      it != p->mon_end(); ++it) {
    Monomial * m = *it;
    Term * t = m->get_term();
    if (!t) continue;
    if (t->get_var_num() <= 0) continue;
    if (!gate(t->get_var_num())->get_input()) continue;

    if (mpz_cmp(m->coeff, half_mod) > 0) {
      Monomial * tmp = new Monomial(minus_one, m->get_term_copy());
      push_mstack_end(tmp);
    } else if (mpz_cmp(m->coeff, half_mod_neg) < 0) {
      Monomial * tmp = new Monomial(one,  m->get_term_copy());
      push_mstack_end(tmp);
    }
  }

  mpz_clear(half_mod);
  mpz_clear(half_mod_neg);

  Polynomial * factor = build_poly();
  if (!factor) return;

  Polynomial * mod = multiply_poly_with_constant(factor, mod_coeff);
  print_pac_mod_rule(file,  factor, mod);

  Polynomial * add = add_poly(mod, p);
  print_pac_add_rule(file,  mod, p, add);

  delete(mod);
  delete(factor);
  delete(add);
}

/*------------------------------------------------------------------------*/

void correct_pp(const Polynomial * p, FILE * file) {
  if (signed_mult) correct_pp_signed(p, file);
  else
    correct_pp_unsigned(p, file);
}

/*------------------------------------------------------------------------*/

const Polynomial * reduce(FILE * file) {
//  if(file) fprintf(file, "reduce\n");
  msg("started reducing");
  Polynomial * rem = 0, * tmp;
  for (int i=NN-1; i>= 0; i--) {
    if (verbose >= 1) msg("reducing by slice %i", i);
    Polynomial * inc_spec = inc_spec_poly(i);

    if (rem) {
      tmp = add_poly(inc_spec, rem);
      delete(inc_spec);
      delete(rem);
      rem = tmp;
    } else {
      rem = inc_spec;
    }

    std::list<Gate*> sl = slices[i];
    for (auto it=sl.begin(); it != sl.end(); ++it) {
      Gate * n = *it;
      if (n->get_elim()) continue;


      if (verbose >= 4  && n->get_gate_constraint()) {
        fputs("[teluma] reducing by ", stdout);
        n->print_gate_constraint(stdout);
      }
      //fprintf(stdout,"reduce by a gate\n");
      tmp = reduce_by_one_gate(rem, n, file);
      delete(n->get_gate_constraint());
      n->set_gate_constraint(0);
      //fprintf(stdout,"mod in reduce\n");
      tmp = mod_poly(tmp, 0, file);
      //fprintf(stdout,"mod in reduce done\n");

      delete(rem);
      rem = tmp;
      if (verbose >= 3) {
        fputs("[teluma] remainder is ", stdout);
        rem->print(stdout);
        msg(" ");
      }
    }

    if (verbose >= 2) {
      msg("after reducing by slice %i", i);
      fprintf(stdout, "[teluma] remainder is ");
      rem->print(stdout);
      msg("");
    }

    if (proof == 1 || proof == 2) {
      Polynomial * pac_poly = add_up_factors(file, proof == 1);
      if (proof == 2){

        print_pac_vector_combi_rule(file, factor_indices, co_factors, pac_poly);
        factor_indices.clear();
        co_factors.clear();
        //fprintf(stdout,"mod in reduce1\n");
        pac_poly = mod_poly(pac_poly, 1, file);
        if (pac_poly->contains_dual_var()) {
           Polynomial * tmp = f_and_l_is_one(pac_poly, 1, file);
           delete(pac_poly);
           pac_poly = tmp;
           //fprintf(stdout,"mod poly in reduce12\n");
           pac_poly = mod_poly(pac_poly, 1, file);
        }

        spec_indices.push_back(pac_poly->get_idx());
      }
      pac_poly->set_level(1);
      spec_of_slice = add_and_merge_factors(file, pac_poly, spec_of_slice, proof == 1);

    }
  }

  if (proof == 1)  {
    Polynomial * res = add_up_spec_of_slice(file, 1);
    res = mod_poly(res, 1, file);
    correct_pp(res, file);
    delete(res);
  } else if (proof == 2) {
    Polynomial * res = add_up_spec_of_slice(file, 0);
    print_pac_vector_add_rule(file, spec_indices, res);
    if (res->contains_dual_var()) {
       Polynomial * tmp = f_and_l_is_one(res, 1, file);
       delete(res);
       res = tmp;

    }
    spec_indices.clear();
    res = mod_poly(res, 1, file);
    correct_pp(res, file);
    delete(res);
  }

  if(!rem->is_constant_zero_poly()) {
    Polynomial * unflipped = unflip_inputs(rem, file);
    delete(rem);
    rem = unflipped;
  }


  return rem;
}

/*------------------------------------------------------------------------*/

bool check_inputs_only(const Polynomial *p) {
  for (std::deque<Monomial*>::const_iterator it=p->mon_begin();
      it != p->mon_end(); ++it) {
    Monomial * m = *it;
    if (!m->get_term()) { continue;
    } else {
      const Var * v = m->get_term()->get_var();
      Gate * n = gate(v->get_num());
      if (!n->get_input()) return 0;
    }
  }
  return 1;
}

/*------------------------------------------------------------------------*/

void write_witness_vector(const Term * t, FILE * file) {
  fputs_unlocked("[teluma]   ", stdout);

  for (unsigned i = 0; i <= NN/2-1; i++) {
    const Var * v = gates[a0+i*ainc]->get_var();

    if (t->contains(v)) {
      fprintf(file, "1");
      fprintf(stdout, "%s = ", v->get_name());
    } else {
      fprintf(file, "0");
    }

    const Var * w = gates[b0+i*binc]->get_var();

    if (t->contains(w)) {
      fprintf(file, "1");
      fprintf(stdout, "%s = ", w->get_name());
    } else {
      fprintf(file, "0");
    }
  }
  fprintf(stdout, "1, all other inputs = 0;\n");
  fprintf(file, "\n");
}

/*------------------------------------------------------------------------*/

void write_witnesses(const Polynomial * p, FILE * file) {
  assert(check_inputs_only(p));

  int len = p->min_term_size();
  if (len == 0) {
    msg("  all inputs = 0;\n");
    for (unsigned i = 0; i <= NN/2-1; i++)
      fprintf(file, "00");

    fprintf(file, "\n");
  } else {
    for (std::deque<Monomial*>::const_iterator it = p->mon_begin();
        it != p->mon_end(); ++it) {
      Monomial * m = *it;
      if (m->get_term()) {
        int tlen = m->get_term_size();
        if (tlen == len) write_witness_vector(m->get_term(), file);
      }
    }
  }
  fprintf(file, ".");
}

/*------------------------------------------------------------------------*/

void generate_witness(const Polynomial * p, const char * name) {
  if (!check_inputs_only(p))
  die("cannot generate witness, as remainder polynomial contains non-inputs");

  #define WITNESSLEN 100
  char witness_name[WITNESSLEN];
  memset(witness_name, '\0', sizeof(witness_name));
  for (int i = 0; name[i] != '.'; i++) {
    witness_name[i] = name[i];
  }
  snprintf(witness_name + strlen(witness_name),
           WITNESSLEN - strlen(witness_name), "%s", ".cex");

  FILE * witness_file;
  if (!(witness_file = fopen(witness_name, "w")))
  die("cannot write output to '%s'", witness_name);

  msg("");
  msg("COUNTER EXAMPLES ARE: ");

  write_witnesses(p, witness_file);

  msg("");
  msg("");
  msg("Counter examples are written to %s", witness_name);
  msg("You can run 'aigsim' from the AIGER library (http://fmv.jku.at/aiger/)");
  msg("to simulate the provided counter example(s).");
  msg("");
  msg("Note: 'aiger/aigsim %s %s' produces output in the form:",
  name, witness_name);
  fputs_unlocked("[teluma] ", stdout);
  if (NN == 2)      fprintf(stdout, "  a[0]b[0]  s[0]\n");
  else if (NN == 4) fprintf(stdout, "  a[0]b[0]a[1]b[1]  s[0]s[1]s[2]s[3]\n");
  else
  fprintf(stdout, "  a[0]b[0]a[1]b[1]...a[%u]b[%u]  s[0]s[1]s[2]...s[%u]\n",
    NN/2-1, NN/2-1, NN-1);

  fclose(witness_file);
}
