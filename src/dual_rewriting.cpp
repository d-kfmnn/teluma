/*------------------------------------------------------------------------*/
/*! \file dual_rewriting.cpp
    \brief contains function to identify the final stage adder

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#include <algorithm>

#include "dual_rewriting.h"
/*------------------------------------------------------------------------*/

std::vector<Gate*> resolved;
std::vector<Polynomial*> resolved_gc;

std::vector<Polynomial*> init_gc;

std::vector<Polynomial*> proof_poly;
Polynomial * target_proof;

std::vector<Term*> mult1v;
std::vector<Term*> remv;
std::vector<Term*> outerv;
std::vector<Polynomial *> target_tmp;
/*------------------------------------------------------------------------*/
static bool compare_poly_with_tail_of_gc(Polynomial * gc, Polynomial * tail){
    if(gc->get_size() != 3) return 0;
    if(tail->get_size() != 2) return 0;

    std::deque<Monomial*>::const_iterator mon_rem = tail->mon_begin();
    for (auto mon = gc->mon_begin()+1; mon != gc->mon_end(); ++mon){
      Monomial * m1 = *mon_rem;
      Monomial * m2 = *mon;
      if (m1->get_term()->cmp(m2->get_term())) return 0;
      mon_rem++;

    }
    return 1;
}

static void update_multv_remv_outerv(Term *m, Term *r, Term *o, Polynomial *p = 0){ //checked
  mult1v.push_back(m);
  remv.push_back(r);
  outerv.push_back(o);
  if(proof) target_tmp.push_back(p->copy());
}

static void add_to_resolved(Gate *g){
  resolved.push_back(g);
  Polynomial * p = gen_gate_constraint(g->get_var_num()/2-1);
  resolved_gc.push_back(p);
}

static int resolved_contain_tail(Term * t){
  Gate * g = gate(t->get_var_num());
  auto it = std::find(resolved.begin(), resolved.end(), g);
  if(it != resolved.end()) return it- resolved.begin();
  return -1;
}

static Term * search_for_poly_in_resolved(Polynomial * rem){
  for (auto i = resolved.begin(); i != resolved.end(); ++i){
    Gate * g = *i;
    Polynomial * gc = g->get_gate_constraint();
    if(gc->get_size() != 3) continue;
    if(compare_poly_with_tail_of_gc(gc, rem)) return gc->get_lt();
  }
  return 0;
}

static void clear_resolved_gc(){
  for(auto it = resolved_gc.begin(); it != resolved_gc.end(); ++it){
    Polynomial * p = *it;
    delete(p);
  }
}

/*------------------------------------------------------------------------*/

static bool is_unit(Gate * g){
  if(g->get_elim()) return 0;
  Polynomial * gc = g->get_gate_constraint();

  if (gc->get_size() > 2) return 0;
  if (gc->get_size() == 1) return 1;

  Term * t = gc->get_tail_term();
  if(t->get_size() == 1) return 1;
  return 0;
}
/*----------------------------------------------------------------------------*/
static void resolve_proof(FILE * file) {
  Polynomial * p1 = target_proof->copy();

  while (!proof_poly.empty()) {
    Polynomial * p2 = proof_poly.back();
    proof_poly.pop_back();


    const Polynomial * negfactor = divide_by_term(p1, p2->get_lt());
    if(!negfactor->is_constant_zero_poly()){
      Polynomial * mult   = multiply_poly_dual_proof(file, negfactor, p2,0);
      Polynomial * rem    = add_poly(p1, mult);
      if (proof == 1 || proof == 2) {
        assert(file);
        print_pac_add_rule(file, p1, mult, rem);
        print_pac_del_rule(file, mult);
      }
      delete(p1);
      delete(mult);
      p1 = rem;
    }
    delete(negfactor);
  }

  delete(target_proof);
  target_proof = p1;
}



static void rewrite_target_proof_by_var(const Var * v, Polynomial * p1, Term* t1, FILE *file){
  Polynomial * p = target_proof->copy();
  Polynomial * sub_gc = p1->copy();
  Polynomial * inv_sub_gc = sub_gc;


  Polynomial * flip = gen_dual_constraint(v);
  Polynomial * min_one = new Polynomial();
  min_one->mon_push_back(new Monomial(minus_one, 0));
  Polynomial * inv_gc = multiply_poly(sub_gc, min_one);
  inv_sub_gc = add_poly(inv_gc, flip);
  if(proof == 1){
    print_pac_mul_rule(file, sub_gc, min_one, inv_gc);
    print_pac_add_rule(file, inv_gc, flip, inv_sub_gc);
    print_pac_del_rule(file, inv_gc);
  } else if(proof == 2){
    print_pac_combi_rule(file, sub_gc, min_one, flip, 0, inv_sub_gc);
  }
  delete(min_one);
  delete(flip);
  delete(inv_gc);


  Polynomial * mul= new Polynomial();
  mul->mon_push_back(new Monomial(one, t1));
  Polynomial * sub_mul = multiply_poly(inv_sub_gc, mul);
  Polynomial * sub_add = add_poly(sub_mul, p);


  if(proof == 1){
    print_pac_mul_rule(file, inv_sub_gc, mul, sub_mul);
    print_pac_add_rule(file, sub_mul, p, sub_add);
  } else if(proof == 2){
    print_pac_combi_rule(file, inv_sub_gc, mul, p, 0, sub_add);
  }
  delete(mul);
  delete(sub_mul);
  delete(p);

  delete(target_proof);
  target_proof = sub_add;

  if(is_unit(gate(v->get_num()))){
    Polynomial * v_gc  = gate(v->get_num())->get_gate_constraint();
    Polynomial * flip = gen_dual_constraint(v);
    Polynomial * tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    target_proof = tmp;

    tmp = reduce_by_one_poly(target_proof, v_gc, file, 0);
    delete(target_proof);
    target_proof = tmp;

    if(v_gc->get_size() == 1) return;

    flip = gen_dual_constraint(v_gc->get_tail_term()->get_var()->get_dual());
    tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    target_proof = tmp;
  }
}




/*----------------------------------------------------------------------------*/

static void remove_var_from_stored_terms(std::vector<Term*> vec, const Var * v){
  for(auto it = vec.begin(); it != vec.end(); ++it){
    Term * t = *it;
    if(!t->contains(v) && !t->contains(v->get_dual())) continue;
    while(t){
      if(t->get_var() != v && t->get_var() != v->get_dual()){
        add_to_vstack(t->get_var());
      } else if (t->get_var() == v){
        clear_vstack();
        break;

      }
      t = t->get_rest();
    }
    Term * new_t = build_term_from_stack(0);
    *it = new_t;
  }
}

static void replace_var_from_stored_terms(std::vector<Term*> vec, const Var * v, const Var * w){
  for(auto it = vec.begin(); it != vec.end(); ++it){
    Term * t = *it;
    if(!t->contains(v) && !t->contains(v->get_dual())) continue;
    while(t){
      if(t->get_var() != v && t->get_var() != v->get_dual()){
        add_to_vstack(t->get_var());
      } else if (t->get_var() == v){
        add_to_vstack(w);
      } else {
        add_to_vstack(w->get_dual());
      }
      t = t->get_rest();
    }
    Term * new_t = build_term_from_stack(0);
    *it = new_t;
  }
}


static void update_stored_terms(Gate * g){
  Polynomial * gc = g->get_gate_constraint();
  if(gc->get_size() == 1){
    remove_var_from_stored_terms(mult1v, g->get_var());
    remove_var_from_stored_terms(remv, g->get_var());
  }
  else if (is_unit(g)){
    replace_var_from_stored_terms(mult1v, g->get_var(), gc->get_tail_term()->get_var());
    replace_var_from_stored_terms(remv, g->get_var(), gc->get_tail_term()->get_var());
  }
}
/*------------------------------------------------------------------------*/

static void eliminate_unit_gate(Gate * n, FILE * file){

  update_stored_terms(n);

  for (auto it_c = n->children_begin(); it_c != n->children_end(); ++it_c) {
    Gate * n_child = *it_c;
    n_child->parents_remove(n);
  }

  for (auto it_p = n->parents_begin(); it_p != n->parents_end(); ++it_p) {
    Gate * n_parent = *it_p;
    eliminate_by_one_gate(n_parent, n, file, 0);
    n_parent->children_remove(n);

    for (auto it_c = n->children_begin(); it_c != n->children_end(); ++it_c) {
      Gate * n_child = *it_c;
      if (!n_parent->is_child(n_child)) n_parent->children_push_back(n_child);
      if (!n_child->is_in_parents(n_parent)) n_child->parents_push_back(n_parent);
    }

    if(is_unit(n_parent)){
      eliminate_unit_gate(n_parent, file);
    }
    else if(n_parent->children_size() == 1 && n_parent->get_gate_constraint()->get_size()==3){
      auto it = n_parent->children_begin();
      Gate * tmp = *it;
      Polynomial * flip = gen_dual_constraint(tmp->get_var());
      Polynomial * rem1 = reduce_by_one_poly(n_parent->get_gate_constraint(), flip, file, 0);
      delete(flip);

      if(rem1->get_size()!=2){
        delete(rem1);
        flip = gen_dual_constraint(tmp->get_var()->get_dual());
        rem1 = reduce_by_one_poly(n_parent->get_gate_constraint(), flip, file, 0);
        delete(flip);
      }
      delete(n_parent->get_gate_constraint());
      n_parent->set_gate_constraint(rem1);
      eliminate_unit_gate(n_parent, file);
    }

  }


  if (verbose>2) msg("removed unit %s", n->get_var_name());
}

/*----------------------------------------------------------------------------*/

//
static void remove_only_positives(FILE * file) { //checked

  msg("remove only positives");
  int counter = 0;
  for (unsigned i=M-1; i >= NN; i--) { //do not even consider changing direction
    Gate * n = gates[i];

    if (n->get_elim()) continue;
    if (!n->get_fsa()) continue;
    if (n->get_pp()) continue;
    if (n->get_gate_constraint()->get_size() > 2) continue;

    bool flag = 0;

    for (auto it_p = n->parents_begin(); it_p != n->parents_end(); ++it_p) {

      Gate * n_parent = *it_p;
      if(n_parent->get_gate_constraint()->get_size() > 2) {
        flag = 1;
        break;
      }

      Monomial * m = n_parent->get_gate_constraint()->get_tail_mon();
      if(!m->get_term()->contains(n->get_var())) {
        flag = 1;
        break;
      }
    }
    if (flag) continue;

    for (auto it_c = n->children_begin(); it_c != n->children_end(); ++it_c) {
      Gate * n_child = *it_c;
      n_child->parents_remove(n);
    }

    for (auto it_p = n->parents_begin(); it_p != n->parents_end(); ++it_p) {
      Gate * n_parent = *it_p;
      eliminate_by_one_gate(n_parent, n, file);

      for (auto it_c = n->children_begin(); it_c != n->children_end(); ++it_c) {
        Gate * n_child = *it_c;
        n_child->parents_push_back(n_parent);
      }
    }


    n->mark_elim();
    delete(n->get_gate_constraint());
    n->set_gate_constraint(0);

    counter++;
    if(verbose >= 3) msg("eliminated %s", n->get_var_name());

  }
  if (verbose >= 1) msg("removed %i positive gates", counter);
}
/*============================================================================*/
static bool do_backward_substitution(Gate * outer, bool first, FILE * file){ //checked
  Gate * inner;
  Polynomial * inner_gc;
  Monomial * inner_m;
  Term * inner_t;

  Polynomial * outer_gc = outer->get_gate_constraint();
  Monomial * outer_m = outer_gc->get_tail_mon();
  Term * outer_t = outer_m->get_term();
  if(first) outer_t = outer_t->get_rest();

  while(outer_t && outer_t->get_ref() == 1) outer_t = outer_t->get_rest();

  if (!outer_t || !outer_t->get_rest()) return 0;

  Gate * tmp = gate(outer_t->get_var_num());


  for(auto it = tmp->parents_begin(); it != tmp->parents_end(); ++it) {
    inner = *it;
    if (inner == outer) continue;
    if (inner->get_elim()) continue;
    if (inner->get_var()->get_level() < outer_t->get_var()->get_level()) break;
    if (inner->get_xor_gate()) continue;

    inner_gc = inner->get_gate_constraint();
    if (inner_gc->get_size() != 2) continue;

    inner_m = inner_gc->get_tail_mon();
    inner_t = inner_m->get_term();
    if (outer_t != inner_t) continue;

    outer_t = outer_m->get_term();
    if(first){
      add_to_vstack(outer_t->get_var());
      outer_t = outer_t->get_rest();
    }
    while(outer_t && outer_t->get_ref() == 1){
      add_to_vstack(outer_t->get_var());
      outer_t = outer_t->get_rest();
    }
    Term * t0 = build_term_from_stack(1);
    Term * t1 = new_term(inner_gc->get_lt()->get_var(), 0);
    Term * t2;
    if(t0) t2 = multiply_term(t0, t1);
    else t2 = t1;


    std::deque<Monomial*>::const_iterator outer_it = outer_gc->mon_begin();
    Monomial * outer_lm = *outer_it;

    push_mstack_end(outer_lm->copy());
    Monomial * tmp = new Monomial(one, t2);
    push_mstack_end(tmp);
    Polynomial * rewr = build_poly();


    if (proof == 1) {
      assert(file);
      Polynomial * tmp = new Polynomial();
      tmp->mon_push_back(new Monomial(minus_one, t0));
      Polynomial * mul_tmp = multiply_poly(inner_gc, tmp);
      print_pac_mul_rule(file, inner_gc, tmp, mul_tmp);

      print_pac_add_rule(file, outer_gc, mul_tmp, rewr);
      print_pac_del_rule(file, mul_tmp);
      delete(tmp);
      delete(mul_tmp);
    } else if (proof == 2) {
      assert(file);
      Polynomial * tmp = new Polynomial();
      tmp->mon_push_back(new Monomial(minus_one, t0));

      print_pac_combi_rule(file, inner_gc, tmp, outer_gc, 0, rewr);
      delete(tmp);
    }

    delete(outer_gc);
    outer->set_gate_constraint(rewr);
    inner->parents_push_back(outer);

    if(verbose > 3)
      msg("substituted %s in %s", inner->get_var_name(), outer->get_var_name());

    return 1;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

static void backward_substitution(FILE * file) { //checked
  msg("backward substitution");

  int counter = 0;

  Gate * outer;
  Polynomial * outer_gc;
  Monomial * outer_m;
  Term * outer_t;

  for (unsigned i = M-2; i >= NN; i--) {
    outer = gates[i];

    if (outer->get_elim()) continue;
    if (outer->get_xor_gate()) continue;
    if (outer->get_pp()) continue;
    if (!outer->get_fsa()) continue;

    outer_gc = outer->get_gate_constraint();
    if (outer_gc->get_size() != 2) continue;

    outer_m = outer_gc->get_tail_mon();
    outer_t = outer_m->get_term();

    if (outer_t->get_size() < 3) continue;

    bool rewr = do_backward_substitution(outer, 1, file);
    while(rewr){
      rewr = do_backward_substitution(outer, 0, file);
    }
    if(is_unit(outer)) eliminate_unit_gate(outer, file);

    counter++;
  }

  if (verbose >= 1) msg("backwards substituted %i gates", counter);
}
/*============================================================================*/

static void remove_positives_in_carry (Gate * n, FILE * file) { // check

    Polynomial * n_gc = n->get_gate_constraint();
    Term * n_t = n_gc->get_tail_term();
    if (n_t->get_size() == n_t->get_dual_count()) return;
    const Var * n_v;
    Gate * child;

    bool flag = 0;

    while(n_t && !flag){
      n_v = n_t->get_var();
      child = gate(n_v->get_num());

      if(child->get_input()) break;

      if(!n_v->is_dual() && child->get_fsa() != 2 && !child->get_pp() &&
        child->get_gate_constraint()->get_size() == 2) {
        eliminate_by_one_gate(n, child, file);

        flag = 1;
        if(verbose >= 3)
          msg("substituted %s in %s", child->get_var_name(), n->get_var_name());

      }
      n_t = n_t->get_rest();
    }

    if(flag) remove_positives_in_carry(n, file);
}
/*----------------------------------------------------------------------------*/

static Term * calc_pivot(Term * t0, Term *t1){ //checked
  while(t0 && t1) {
    if (t0->get_var() == t1->get_var()){
      add_to_vstack(t0->get_var());
      t0 = t0->get_rest();
      t1 = t1->get_rest();
    } else if (t0->get_var_level() > t1->get_var_level()){
      t0 = t0->get_rest();
    } else {
      t1 = t1->get_rest();
    }
  }
  Term * res = build_term_from_stack();
  return res;
}

/*----------------------------------------------------------------------------*/

static const Var * search_for_tail_in_init(Term * t){
  assert(t);
  for(auto it = init_gc.begin(); it != init_gc.end(); ++it){
    Polynomial * gc = *it;
    if (t == gc->get_tail_term()) return gc->get_lt()->get_var();
  }
  return 0;
}

static int search_for_tail_in_init_ind(Term * t){
  assert(t);
  for(auto it = init_gc.begin(); it != init_gc.end(); ++it){
    Polynomial * gc = *it;
    if (t == gc->get_tail_term()) return it - init_gc.begin();
  }
  return 0;
}

static const Var * search_for_tail(Term * t){
  assert(t);
  Gate * g = gate(t->get_var_num());
  for(auto it = g->parents_begin(); it != g->parents_end(); ++it){
    Gate * parent = *it;
    Polynomial * gc = parent->get_gate_constraint();
    if (gc->get_size() != 2) continue;
    if (t == gc->get_tail_term()) return parent->get_var();
  }
  return 0;
}

static const Var * search_for_tail_in_resolved(Term * t){
  for(auto it = resolved.begin(); it != resolved.end(); ++it){
    Gate * g = *it;
    int index = it - resolved.begin();
    Polynomial * gc = resolved_gc[index];
    if (gc->get_size() != 2) continue;

    if (t == gc->get_tail_term()) return g->get_var();
  }
  return 0;
}



static int search_for_tail_in_resolved_ind(Term * t){
  for(auto it = resolved.begin(); it != resolved.end(); ++it){
    int index = it - resolved.begin();
    Polynomial * gc = resolved_gc[index];
    if (gc->get_size() != 2) continue;

    if (t == gc->get_tail_term()) return index;
  }
  return 0;
}


static Term * backward_rewrite_term(FILE * file, Term *t, Term * piv = 0,  int larger_pivot = 0){
  if(t->get_size() == 1) return t->copy();
  const Var * tail;
  std::vector<const Var*> remainder;
  std::vector<const Var*> remainder2;


  while(t){
    if(t->get_ref() > 1){
      tail = search_for_tail(t);
      if(tail) {
        remainder.push_back(tail);
        break;
      }
    }
    remainder.push_back(t->get_var());
    remainder2.push_back(t->get_var());
    t = t->get_rest();
  }
  Term * quo = sort_and_build_term_from_vector(remainder);

  if(proof && larger_pivot && tail){
      Polynomial * tail_gc = gate(tail->get_num())->get_gate_constraint();
      Term * rem = sort_and_build_term_from_vector(remainder2);
      Term * rem2 = multiply_term(rem, piv);
      Polynomial * tmp = new Polynomial();
      if (larger_pivot == 1) tmp->mon_push_back(new Monomial(one, rem2));
      else if(larger_pivot == -1)tmp->mon_push_back(new Monomial(minus_one, rem2));
      Polynomial * mul_proof = multiply_poly(tail_gc, tmp);
      Polynomial * add = add_poly(target_proof, mul_proof);

      if(proof == 1){
        print_pac_mul_rule(file, tail_gc, tmp, mul_proof);
        print_pac_add_rule(file, target_proof, mul_proof, add);
        print_pac_del_rule(file, mul_proof);
      } else if (proof == 2){
        print_pac_combi_rule(file, tail_gc, tmp, target_proof, 0, add);
      }
      delete(target_proof);
      target_proof = add;
      delete(tmp);

  }
  return quo;
}

Term * backward_rewrite_term_until_completion(FILE * file, Term * t, Term * rem = 0, int larger_pivot = 0){
  if(t->get_size() == 1) return t;
  Term * tmp = backward_rewrite_term(file, t, rem, larger_pivot);
  while(tmp != t) {
    deallocate_term(t);
    t  = tmp;
    tmp = backward_rewrite_term(file, t, rem, larger_pivot);
  }
  deallocate_term(t);
  return tmp;
}


static Term * expand_term(Term *t, FILE * file = 0, bool update = 0, Gate * g = 0){
  Term * tail;
  std::vector<const Var*> remainder;

  while(t){
    if(!t->get_var()->is_dual()){
      Polynomial * p = gate(t->get_var_num())->get_gate_constraint();

      if(proof && update && g){
        Polynomial * gc = g->get_gate_constraint();
        Polynomial * tmp = reduce_by_one_poly(gc, p, file, 0);
        delete(gc);
        g->set_gate_constraint(tmp);
      } else if(proof && update){
        Polynomial * tmp = reduce_by_one_poly(target_proof, p, file, 0);
        delete(target_proof);
        target_proof = tmp;
      }

      if(p->get_size() != 2) return t;
      tail = p->get_tail_term();
      while(tail) {
        remainder.push_back(tail->get_var());
        tail = tail->get_rest();
      }
    }
    else remainder.push_back(t->get_var());
    t = t->get_rest();
  }
  Term * quo = sort_and_build_term_from_vector(remainder);
  return quo;
}

static Term * expand_term_until_completion(Term * t, FILE * file = 0, bool update = 0){
  Term * tmp = expand_term(t, file, update);
  while(tmp != t) {
    deallocate_term(t);
    t  = tmp;
    tmp = expand_term(t, file, update);
  }
  deallocate_term(t);
  return tmp;
}



static Term * divide_tail_term_by_pivot(Gate *g, Term * t, FILE *file){
  Polynomial * g_gc = g->get_gate_constraint();
  if (g_gc->get_size() != 2) return 0;
  Term * t0 = g_gc->get_tail_term();
  Term * rem = remainder_t (t0, t);

   if(rem && !proof){
     if(rem->get_size() > 1)
      rem = backward_rewrite_term_until_completion(file, rem);
   } else if(rem){
    Polynomial * flip = gen_dual_constraint(g->get_var());
    Polynomial * min_one = new Polynomial();
    min_one->mon_push_back(new Monomial(minus_one, 0));
    Polynomial * inv_gc = multiply_poly(g_gc, min_one);
    Polynomial * add = add_poly(inv_gc, flip);

     if(proof == 1){
       print_pac_mul_rule(file, g_gc, min_one, inv_gc);
       print_pac_add_rule(file, inv_gc, flip, add);
       print_pac_del_rule(file, inv_gc);
     } else if (proof == 2){
       print_pac_combi_rule(file, g_gc, min_one, flip, 0, add);
     }

    delete(min_one);
    if(rem->get_size()==1){


      delete(flip);
      delete(inv_gc);
      Polynomial * flip_t = gen_dual_constraint(rem->get_var());
      Polynomial * poly_t = new Polynomial();
      poly_t->mon_push_back(new Monomial(minus_one, t->copy()));
      Polynomial * mul_t = multiply_poly(flip_t, poly_t);

      Polynomial * add_t = add_poly(add, mul_t);
      if(proof == 1){
        print_pac_mul_rule(file, flip_t, poly_t, mul_t);
        print_pac_add_rule(file, add, mul_t, add_t);
      } else if (proof == 2){
          print_pac_combi_rule(file, flip_t, poly_t, add, 0, add_t);
      }

      print_pac_del_rule(file, add);
      delete(add);
      delete(poly_t);
      delete(flip_t);
      delete(mul_t);
      proof_poly.push_back(add_t);

    } else {
      rem = backward_rewrite_term_until_completion(file, rem);
      if(rem->get_size() == 1){
         Polynomial * rem_gc = gate(rem->get_var_num())->get_gate_constraint();
         Polynomial * poly_t = new Polynomial();
         poly_t->mon_push_back(new Monomial(one, t->copy()));
         Polynomial * mul_t = multiply_poly(rem_gc, poly_t);

         Polynomial * add_t = add_poly(add, mul_t);
         if(proof == 1){
           print_pac_mul_rule(file, rem_gc, poly_t, mul_t);
           print_pac_add_rule(file, add, mul_t, add_t);
         } else if (proof == 2){
             print_pac_combi_rule(file, rem_gc, poly_t, add, 0, add_t);
         }

         Polynomial * flip_t2 = gen_dual_constraint(rem->get_var());
         Polynomial * poly_t2 = new Polynomial();
         poly_t2->mon_push_back(new Monomial(minus_one, t->copy()));
         Polynomial * mul_t2 = multiply_poly(flip_t2, poly_t2);

         Polynomial * add_t2 = add_poly(add_t, mul_t2);
         if(proof == 1){
           print_pac_mul_rule(file, flip_t2, poly_t2, mul_t2);
           print_pac_add_rule(file, add_t, mul_t2, add_t2);
         } else if (proof == 2){
             print_pac_combi_rule(file, flip_t2, poly_t2, add_t, 0, add_t2);
         }


         proof_poly.push_back(add_t2);


      }

      else   proof_poly.push_back(add);


    }
  }
  return rem;
}

static bool term_vector_contains_only_singles(std::vector<Term*> vec){
  for(auto i = vec.begin(); i != vec.end(); ++i){
    Term * tmp = *i;
    if(tmp->get_size()!= 1) return 0;
  }
  return 1;
}

/*-----------------------------------------------------------------------------*/

static void expand_tail_term_and_update_gc (Gate *g, FILE * file = 0){ //check
  Polynomial * gc = g->get_gate_constraint();

  if(gc->get_size() != 2) return;
  Term * t = gc->get_tail_term();
  Term * t_exp;
  if(proof && file) t_exp = expand_term(t, file, 1 ,g);
  else {
    t_exp = expand_term(t);

    push_mstack(new Monomial(minus_one, t->copy()));
    push_mstack(new Monomial(one, t_exp->copy()));

    Polynomial * p = build_poly();
    Polynomial * add = add_poly(gc, p);
    delete(p);
    delete(gc);
    g->set_gate_constraint(add);
  }
}

static void expand_tail_term_until_contains_and_update_gc (Gate *g, const Var * tail, FILE * file){ //check
  Polynomial * gc = g->get_gate_constraint();

  if(gc->get_size() != 2) return;
  Term * t = gc->get_tail_term();
  Term * t_exp = t;
  while (!t_exp->contains(tail)){
    t = t_exp;
    t_exp = expand_term(t, file, 1 ,g);
  }

}



static Term * carry_skip_rewriting(FILE * file, Term * head, Term * tail, Term * pivot, Term * rem){

  auto it = find(outerv.begin(), outerv.end(), tail);
  if(it == outerv.end()) return 0;
  int index = it - outerv.begin();
  Polynomial * unrolled_gc = gate(outerv[index]->get_var_num())->get_gate_constraint();
  Polynomial * unrolled_gc2 = gate(tail->get_var_num())->get_gate_constraint();
  Term * unrolled_tail = remv[index];
  Term * unrolled_head = mult1v[index];

  if(proof){
    Polynomial * tmp1 = reduce_by_one_poly(target_proof, unrolled_gc, file, 0);
    delete(target_proof);
    target_proof = tmp1;
  }


  if(unrolled_tail->get_size()==1 && unrolled_head->get_size() == 2 &&
     head->contains(unrolled_tail->get_var()->get_dual())){

     Polynomial * p = build_one_minus_x_times_y_poly(unrolled_head, unrolled_tail);
     Term * found = search_for_poly_in_resolved(p);
     delete(p);
     if(proof){

       Term * x0 = multiply_term(pivot, rem);
       Polynomial * tmp_x0 = new Polynomial();
       tmp_x0->mon_push_back(new Monomial(minus_one, x0));
       Polynomial * mul_proof2 = multiply_poly(unrolled_gc2, tmp_x0);
       Polynomial * add2 = add_poly(target_proof, mul_proof2);

       if(proof == 1){
         print_pac_mul_rule(file, unrolled_gc2, tmp_x0, mul_proof2);
         print_pac_add_rule(file, target_proof, mul_proof2, add2);
         print_pac_del_rule(file, mul_proof2);
       } else if (proof == 2){
         print_pac_combi_rule(file, unrolled_gc2, tmp_x0, target_proof, 0, add2);
       }
       Polynomial * flip = gen_dual_constraint(tail->get_var()->get_dual());
       Polynomial * res = reduce_by_one_poly(add2, flip, file, 0);
       delete(target_proof);
       target_proof = res;

     }
     if(found) return found;
  }

  Term * unrolled_pivot = calc_pivot(head, unrolled_head);
  if(!unrolled_pivot) return 0;


  Term * t0 = remainder_t(unrolled_head, unrolled_pivot);

  if(t0 && (t0->get_size() != 1 || !t0->get_var()->is_dual())) return 0;

  if(t0) {
    Term * t0_flipped = new_term(t0->get_var()->get_dual(),0);
    t0 = t0_flipped; // TODO flip?

    if(proof){
      Polynomial * flip_t0 = gen_dual_constraint(t0->get_var());
      Polynomial * tmp1 = reduce_by_one_poly(target_proof, flip_t0, file, 0);
      delete(target_proof);
      target_proof = tmp1;

    }



 } else {
    if (unrolled_head->get_size() == 2) {
      Polynomial * p = build_one_minus_x_times_y_poly(unrolled_head, unrolled_tail);

      Term * found = search_for_poly_in_resolved(p);
      delete(p);
      if(proof){

        Term * x0 = multiply_term(pivot, rem);
        Polynomial * tmp_x0 = new Polynomial();
        tmp_x0->mon_push_back(new Monomial(minus_one, x0));
        Polynomial * mul_proof2 = multiply_poly(unrolled_gc2, tmp_x0);
        Polynomial * add2 = add_poly(target_proof, mul_proof2);

        if(proof == 1){
          print_pac_mul_rule(file, unrolled_gc2, tmp_x0, mul_proof2);
          print_pac_add_rule(file, target_proof, mul_proof2, add2);
          print_pac_del_rule(file, mul_proof2);
        } else if (proof == 2){
          print_pac_combi_rule(file, unrolled_gc2, tmp_x0, target_proof, 0, add2);
        }
        Polynomial * flip = gen_dual_constraint(tail->get_var()->get_dual());
        Polynomial * res = reduce_by_one_poly(add2, flip, file, 0);
        delete(target_proof);
        target_proof = res;

      }
      if(found) return found;

    }
  }

  Term * t1 = remainder_t(head, unrolled_pivot);

  Term * quo = 0;



  if(t1->get_size() > 1){
    Term * u_p = multiply_term(pivot, unrolled_pivot);
    Term * u_r = multiply_term(rem, unrolled_tail);
     Term * found = carry_skip_rewriting(file, t1, t0, u_p, u_r);
     if(!found) return 0;
     quo = new_term(found->get_var()->get_dual(), 0);

  } else {
    if(proof){
      Polynomial * flip_t1 = gen_dual_constraint(t1->get_var()->get_dual());
      Polynomial * tmp1 = reduce_by_one_poly(target_proof, flip_t1, file, 0);
      delete(target_proof);
      target_proof = tmp1;
    }

    std::vector<const Var*> tmp;
    tmp.push_back(t0->get_var());
    tmp.push_back(t1->get_var()->get_dual());
    quo = sort_and_build_term_from_vector(tmp);

    int idx = resolved_contain_tail(t0);
    Gate * parent = resolved[idx];
    Polynomial * parent_gc = resolved_gc[idx];
    const Var * child = quo->get_rest()->get_var();
    if(parent_gc->get_size() == 2 && parent_gc->get_tail_term()->contains(child)){
        deallocate_term(quo);
        quo = new_term(parent->get_var()->get_dual(), 0);

        if(proof){

          Polynomial * parent_gc = gen_gate_constraint(t0->get_var_num()/2-1);
          Polynomial * tmp_proof = reduce_by_one_poly(target_proof, parent_gc, file, 0);
          Term * x0 = multiply_term(pivot, rem);
          Term * x1 = multiply_term(unrolled_tail, unrolled_pivot);
          Term * x2 = multiply_term(x0, x1);
          Polynomial * tmp = new Polynomial();
          tmp->mon_push_back(new Monomial(minus_one, x2));
          Polynomial * mul_proof = multiply_poly(parent_gc, tmp);
          Polynomial * add = add_poly(tmp_proof, mul_proof);

          if(proof == 1){
            print_pac_mul_rule(file, parent_gc, tmp, mul_proof);
            print_pac_add_rule(file, tmp_proof, mul_proof, add);
            print_pac_del_rule(file, mul_proof);
          } else if (proof == 2){
            print_pac_combi_rule(file, parent_gc, tmp, tmp_proof, 0, add);
          }
          print_pac_del_rule(file, tmp_proof);
          Polynomial * flip = gen_dual_constraint(t0->get_var()->get_dual());
          Polynomial * tmp_proof2 = reduce_by_one_poly(add, flip, file, 0);
          print_pac_del_rule(file, add);
          delete(flip);

          delete(target_proof);
          target_proof = tmp_proof2;
      }
    }
  }

  Term * new_head = multiply_term(unrolled_pivot, quo);



  if (new_head->get_size() == 2) {
    Polynomial * p = build_one_minus_x_times_y_poly(new_head, unrolled_tail);
    Term * found = search_for_poly_in_resolved(p);

    if(proof){

      Term * x0 = multiply_term(pivot, rem);
      Polynomial * tmp_x0 = new Polynomial();
      tmp_x0->mon_push_back(new Monomial(minus_one, x0));
      Polynomial * mul_proof2 = multiply_poly(unrolled_gc2, tmp_x0);
      Polynomial * add2 = add_poly(target_proof, mul_proof2);

      if(proof == 1){
        print_pac_mul_rule(file, unrolled_gc2, tmp_x0, mul_proof2);
        print_pac_add_rule(file, target_proof, mul_proof2, add2);
        print_pac_del_rule(file, mul_proof2);
      } else if (proof == 2){
        print_pac_combi_rule(file, unrolled_gc2, tmp_x0, target_proof, 0, add2);
      }
      Polynomial * flip = gen_dual_constraint(tail->get_var()->get_dual());
      Polynomial * res = reduce_by_one_poly(add2, flip, file, 0);




      delete(target_proof);
      target_proof = res;

    }


    delete(p);
    if(found) return found;

  }
  return 0;

}

static Term * get_all_but_last_var_of_term(Term *t){
  while(t->get_rest()){
    add_to_vstack(t->get_var());
    t = t->get_rest();
  }
  return build_term_from_stack(0);
}

static Term * get_last_var_of_term(Term *t){
  while(t->get_rest()){
    t = t->get_rest();
  }
  return new_term(t->get_var(), 0);
}


static Term * expand_head_to_find(FILE * file, Term * head, Term * tail, Term * res){
  if (head->get_size() == 1) return 0;
  if (tail->get_size() != 1) return 0;
  if (tail->get_var()->is_dual()) return 0;

  Term * tail_exp = expand_term_until_completion(tail);
  Term * head_h = get_all_but_last_var_of_term(head);
  Term * head_t = get_last_var_of_term(head);

  int idx = resolved_contain_tail(head_t);
  if(idx == -1) return 0;

  Polynomial * gc = resolved_gc[idx];
  Term * gc_t = gc->get_tail_term();

  Term * t0 = multiply_term(head_h, new_term(gc_t->get_var()->get_dual(), 0));
  Term * t1 = multiply_term(head_h, new_term(gc_t->get_rest()->get_var()->get_dual(), 0));

  t0 = backward_rewrite_term_until_completion(file, t0);
  if(t0->get_size() > 1) return 0;
  t0 = new_term(t0->get_var()->get_dual(),0);

  t1 = backward_rewrite_term_until_completion(file, t1);
  if(t1->get_size() > 1) return 0;
  t1 = new_term(t1->get_var()->get_dual(),0);



  Term * t2 = multiply_term(t0, t1);
//  deallocate_term(t0);
//  deallocate_term(t1);

  Term * final = multiply_term(tail_exp, t2);
//  deallocate_term(t2);

  const Var * v = search_for_tail_in_init(final);
//  deallocate_term(final);

  if(v && !proof)  return new_term(v,0);
  else if (v){
    Polynomial * tail_gc = gate(tail->get_var_num())->get_gate_constraint();
    Polynomial * tmp = reduce_by_one_poly(target_proof, tail_gc, file, 0);
    delete(target_proof);
    target_proof = tmp;

    Polynomial * flip = gen_dual_constraint(gc->get_lt()->get_var());
    tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    delete(flip);
    target_proof = tmp;

    tmp = reduce_by_one_poly(target_proof, gc, file, 0);
    delete(target_proof);
    target_proof = tmp;

    flip = gen_dual_constraint(gc_t->get_var()->get_dual());
    tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    delete(flip);
    target_proof = tmp;

    flip = gen_dual_constraint(gc_t->get_rest()->get_var()->get_dual());
    tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    delete(flip);
    target_proof = tmp;

    expand_tail_term_until_contains_and_update_gc(gate(t0->get_var_num()), gc_t->get_var()->get_dual(), file);
    expand_tail_term_until_contains_and_update_gc(gate(t1->get_var_num()), gc_t->get_rest()->get_var()->get_dual(), file);
    Polynomial * t0_gc = gate(t0->get_var_num())->get_gate_constraint();
    Polynomial * t1_gc = gate(t1->get_var_num())->get_gate_constraint();


    Term * t_0 = multiply_term(res, tail_exp);
    Term * t_1 = multiply_term(t_0, head_h);
    Term * t_2 = multiply_term(t_1, new_term(gc_t->get_rest()->get_var()->get_dual(),0));
    Polynomial * p1 = new Polynomial();
    p1->mon_push_back(new Monomial(one, t_0));
    p1->mon_push_back(new Monomial(minus_one, t_2));
    Polynomial * mul_p1 = multiply_poly(t0_gc, p1);
    Polynomial * add_p1 = add_poly(target_proof, mul_p1);

    if(proof == 1){
      print_pac_mul_rule(file, t0_gc, p1,mul_p1);
      print_pac_add_rule(file, mul_p1, target_proof, add_p1);
    } else if (proof == 2) {
      print_pac_combi_rule(file, t0_gc, p1, target_proof, 0, add_p1);
    }
    delete(target_proof);
    target_proof = add_p1;

    Term * t_3 = multiply_term(t_0, t0_gc->get_lt());
    Polynomial * p12 = new Polynomial();
    p12->mon_push_back(new Monomial(one, t_0));
    p12->mon_push_back(new Monomial(minus_one, t_3));
    Polynomial * mul_p12 = multiply_poly(t1_gc, p12);
    Polynomial * add_p12 = add_poly(target_proof, mul_p12);

    if(proof == 1){
      print_pac_mul_rule(file, t1_gc, p12,mul_p12);
      print_pac_add_rule(file, mul_p12, target_proof, add_p12);
    } else if (proof == 2) {
      print_pac_combi_rule(file, t1_gc, p12, target_proof, 0, add_p12);
    }
    delete(target_proof);
    target_proof = add_p12;

    flip = gen_dual_constraint(t0_gc->get_lt()->get_var()->get_dual());
    tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    delete(flip);
    target_proof = tmp;

    flip = gen_dual_constraint(t1_gc->get_lt()->get_var()->get_dual());
    tmp = reduce_by_one_poly(target_proof, flip, file, 0);
    delete(target_proof);
    delete(flip);
    target_proof = tmp;

    int indx = search_for_tail_in_init_ind(final);
    rewrite_target_proof_by_var(v, init_gc[indx], res, file);

    return new_term(v,0);
  }
  return 0;
}


static Term * second_level_rewriting(std::vector<Term*> vec, Term * pivot, Term * rem, FILE * file){
  Term * head = vec.front()->get_size() > vec.back()->get_size() ? vec.front() : vec.back();
  Term * tail = vec.front()->get_size() < vec.back()->get_size() ? vec.front() : vec.back();

  if (tail->get_size() != 1) return 0;

  Term * tail_flip = new_term(tail->get_var()->get_dual(), 0);
  deallocate_term(tail);
  tail = tail_flip;

  if(!tail->get_var()->is_dual() && resolved_contain_tail(tail) != -1){
     Term * found = carry_skip_rewriting(file, head, tail, pivot, rem);
     if(found) return found;
  }

  if (head->get_size() == 2) {
    Polynomial * p = build_one_minus_x_times_y_poly(head, tail);
    Term * found = search_for_poly_in_resolved(p);
    if(found && proof){
      Term * t1 = multiply_term(pivot, rem);
      rewrite_target_proof_by_var(found->get_var(),  gate(found->get_var_num())->get_gate_constraint(), t1, file);

    }
    delete(p);
    if(found) return found;
  }

  auto it = find(mult1v.begin(), mult1v.end(), head);
  if(it == mult1v.end()) {
    head = expand_term(head, file, 1);
    it = find(mult1v.begin(), mult1v.end(), head);
    if(it == mult1v.end()) {
      Term * t0 = multiply_term(pivot, rem);
      return expand_head_to_find(file, head, tail, t0);
    }
  }
  int index = it - mult1v.begin();

  Polynomial * p = gate(tail->get_var_num())->get_gate_constraint();
  if(p->get_size() != 2) return 0;
  if (remv[index] == p->get_tail_term()) {
    if(proof){
      Polynomial * tmp = reduce_by_one_poly(target_proof, p, file, 0);
      Term * t0 = multiply_term(pivot, rem);
      Polynomial * tmp1 = new Polynomial();
      tmp1->mon_push_back(new Monomial(minus_one, t0));
      Polynomial * mult = multiply_poly(target_tmp[index], tmp1);
      Polynomial * add = add_poly(tmp, mult);

      if(proof == 1){
        print_pac_mul_rule(file, target_tmp[index], tmp1, mult);
        print_pac_add_rule(file, tmp, mult, add);
        print_pac_del_rule(file, mult);
      } else if (proof == 2){
        print_pac_combi_rule(file, target_tmp[index], tmp1, tmp, 0, add);
      }

      Polynomial * flip = gen_dual_constraint(outerv[index]->get_var()->get_dual());
      Polynomial * res = reduce_by_one_poly(add, flip, file, 0);
      delete(target_proof);
      target_proof = res;

    }

    return outerv[index];
  }

  Term * tail_exp = expand_term_until_completion(tail, file, 1);
  if (remv[index] == tail_exp) {
    if(proof) {
      Term * t0 = multiply_term(pivot, rem);
      Polynomial * tmp1 = new Polynomial();
      tmp1->mon_push_back(new Monomial(minus_one, t0));
      Polynomial * mult = multiply_poly(target_tmp[index], tmp1);
      Polynomial * add = add_poly(target_proof, mult);

      if(proof == 1){
        print_pac_mul_rule(file, target_tmp[index], tmp1, mult);
        print_pac_add_rule(file, target_proof, mult, add);
        print_pac_del_rule(file, mult);
      } else if (proof == 2){
        print_pac_combi_rule(file, target_tmp[index], tmp1, target_proof, 0, add);
      }

      Polynomial * flip = gen_dual_constraint(outerv[index]->get_var()->get_dual());
      Polynomial * res = reduce_by_one_poly(add, flip, file, 0);
      delete(target_proof);
      target_proof = res;


    }
    return outerv[index];
  }
  return 0;

}

/*-----------------------------------------------------------------------------*/
static bool size_three_vec_first_has_size_two(std::vector<Term*> vec){
  if(vec.size() != 3) return 0;
  if(vec.front()->get_size() != 2) return 0;
  if(vec[1]->get_size()!= 1 || vec[2]->get_size()!= 1) return 0;
  return 1;
}

static bool size_three_vec_first_has_size_three(std::vector<Term*> vec){
  if(vec.size() != 3) return 0;
  if(vec.front()->get_size() != 3) return 0;
  if(vec[1]->get_size()!= 1 || vec[2]->get_size()!= 1) return 0;
  return 1;
}
/*----------------------------------------------------------------------------*/


static void expand_first_two(Term * t, FILE * file = 0){
  if (t->get_size() <= 2) return;

  Gate * g0 = gate(t->get_var_num());
  Gate * g1 = gate(t->get_rest()->get_var_num());
  expand_tail_term_and_update_gc(g0, file);
  expand_tail_term_and_update_gc(g1, file);
}
/*-----------------------------------------------------------------------------*/

static std::vector<Term*> internal_pivot_calc (FILE *file, Term * outer, Term * pivot, Term * carry = 0){
  std::vector<const Var*> remainder;
  std::vector<Term*> quotient;
  std::vector<Term*> res;
  Term * outer_t = outer;

  if(carry) quotient.push_back(carry);
  if(proof && carry && carry->get_size() == 1){
    Polynomial * flip = gen_dual_constraint(carry->get_var()->get_dual());
    Polynomial * tmp = reduce_by_one_poly(target_proof, flip, file,0);
    delete(target_proof);
    target_proof = tmp;
  }

  while(outer_t){
    Term * t0 = divide_tail_term_by_pivot(gate(outer_t->get_var_num()), pivot, file);

    if(t0) {
      quotient.push_back(t0);
    } else {
      remainder.push_back(outer_t->get_var());
    }
    outer_t = outer_t->get_rest();
  }
  Term * rem = sort_and_build_term_from_vector(remainder);

  if(proof) resolve_proof(file);


  Term * quo;
  if(term_vector_contains_only_singles(quotient)){
    quo = gen_dual_term_from_vector(quotient);
  } else {
    Term * tmp_t = 0;
    if(quotient.size() == 2) {
      tmp_t = second_level_rewriting(quotient, pivot, rem, file);
      if(!tmp_t) return res;
      quo = new_term(tmp_t->get_var()->get_dual(), 0);


    } else if (size_three_vec_first_has_size_two(quotient) && !carry) {
      Gate * g = gate(outer->get_rest()->get_var_num());
      Polynomial * g_gc = g->get_gate_constraint();
      Gate * g1 = gate(g_gc->get_tail_term()->get_rest()->get_var_num());
      if(!g1->get_xor_gate()) eliminate_by_one_gate(g, g1, file);
      return res;

    } else if (size_three_vec_first_has_size_three(quotient)){
      Gate * g = gate(outer->get_var_num());
      expand_tail_term_and_update_gc(g, file);
      return res;

    } else return res;
  }

 if(quo && quo->get_size() == 2 && !quo->get_var()->is_dual()){
   Gate * parent = gate(quo->get_var_num());
   Polynomial * parent_gc = parent->get_gate_constraint();
   const Var * child = quo->get_rest()->get_var();
   if(parent_gc->get_size() == 2 && parent_gc->get_tail_term()->contains(child)){
     deallocate_term(quo);
     quo = new_term(parent->get_var()->get_dual(), 0);

     if(proof){
       Polynomial * tmp_proof = reduce_by_one_poly(target_proof, parent_gc, file, 0);
       Term * t0 = multiply_term(pivot, rem);
       Polynomial * tmp = new Polynomial();
       tmp->mon_push_back(new Monomial(minus_one, t0));
       Polynomial * mul_proof = multiply_poly(parent_gc, tmp);
       Polynomial * add = add_poly(tmp_proof, mul_proof);

       if(proof == 1){
         print_pac_mul_rule(file, parent_gc, tmp, mul_proof);
         print_pac_add_rule(file, tmp_proof, mul_proof, add);
         print_pac_del_rule(file, mul_proof);
       } else if (proof == 2){
         print_pac_combi_rule(file, parent_gc, tmp, tmp_proof, 0, add);
       }
       print_pac_del_rule(file, tmp_proof);
       Polynomial * flip = gen_dual_constraint(parent->get_var()->get_dual());
       Polynomial * tmp_proof2 = reduce_by_one_poly(add, flip, file, 0);
       print_pac_del_rule(file, add);
       delete(flip);
       delete(target_proof);
       target_proof = tmp_proof2;
     }
   }
 }

 if(quo && quo->get_size() > 1) {

   const Var * v = search_for_tail(quo);
   if(v && proof) {
     Term * t1 = multiply_term(pivot, rem);
     if(!rem) t1 = pivot;
     rewrite_target_proof_by_var(v, gate(v->get_num())->get_gate_constraint(), t1, file);
  }
  if(!v){
    v = search_for_tail_in_resolved(quo);
    if(v && proof) {
      int indx = search_for_tail_in_resolved_ind(quo);
      Term * t1 = multiply_term(pivot, rem);
      if(!rem) t1 = pivot;
      rewrite_target_proof_by_var(v, resolved_gc[indx], t1, file);
   }
  }

   if(!v){
     Term * t1 = multiply_term(pivot, rem);
     if(!rem) t1 = pivot;
     Term * tmp = backward_rewrite_term(file, quo, t1, -1);

     v = search_for_tail(tmp);
     if(v && proof) {
       Term * t1 = multiply_term(pivot, rem);
       if(!rem) t1 = pivot;
       rewrite_target_proof_by_var(v, gate(v->get_num())->get_gate_constraint(), t1, file);
    }

     if(!v) {
       v = search_for_tail_in_resolved(tmp);
       if(v && proof) {
         int indx = search_for_tail_in_resolved_ind(tmp);
         Term * t1 = multiply_term(pivot, rem);
         if(!rem) t1 = pivot;
         rewrite_target_proof_by_var(v, resolved_gc[indx], t1, file);
      }
     }


     if(!v) {
       v = search_for_tail_in_init(tmp);
       if(v && proof){
         int indx = search_for_tail_in_init_ind(tmp);
         Term * t1 = multiply_term(pivot, rem);
         if(!rem) t1 = pivot;
         rewrite_target_proof_by_var(v, init_gc[indx], t1, file);
       }
     }
   }

   if(v) {
     deallocate_term(quo);
     quo = new_term(v->get_dual(), 0);
   }
 }

 if(quo && quo->get_size() == 1){
   Gate * g = gate(quo->get_var_num());
   if(g->get_gate_constraint()->get_size() == 1){
     deallocate_term(quo);
     quo = 0;
   }
 }

 res.push_back(quo);
 res.push_back(rem);
 return res;

}

/*-----------------------------------------------------------------------------*/


static std::vector<Term *> larger_pivot_rewriting(FILE *file, Term * mul, Term * rem){
  mul = backward_rewrite_term_until_completion(file, mul, rem, 1);
  std::vector<Term*> rewritten;

  Term * pivot =  calc_pivot(mul, gate(rem->get_var_num())->get_gate_constraint()->get_tail_term());

  if(!pivot) {
    rewritten.push_back(mul->copy());
    rewritten.push_back(rem->copy());
    return rewritten;
  }

  Term * carry = remainder_t(mul, pivot);

  std::vector<Term*> res = internal_pivot_calc(file, rem, pivot, carry);
  if(res.empty()) return rewritten;

  Term * new_sub;

  if(res.front()) new_sub = multiply_term(pivot, res.front());
  else new_sub = pivot;
  new_sub = backward_rewrite_term_until_completion(file, new_sub, res.back(), 1);

  rewritten.push_back(new_sub);
  rewritten.push_back(res.back());
  return rewritten;
}

/*----------------------------------------------------------------------------*/
static int pivot_rewriting(Gate * outer, Term * pivot, FILE * file){
  Polynomial * outer_gc = outer->get_gate_constraint();
  Term * outer_t = outer_gc->get_tail_term();

  // first step where all come from outer_t
  std::vector<Term*> res = internal_pivot_calc(file, outer_t, pivot);
  if(res.empty()) return 0;
  Term * sub = res.front();
  Term * rem = res.back();

  Term * mult1 = 0, * mult2, * mult3 = 0;
  bool larger_sub = 0;

  if(sub && sub->get_size() == 1 && is_unit(gate(sub->get_var_num()))){
    Polynomial * gc = gate(sub->get_var_num())->get_gate_constraint();
    Term * tail = gc->get_tail_term();
    Term * sub_tmp = 0;
    if (sub->get_var()->is_dual())
      sub_tmp = new_term(tail->get_var()->get_dual(), 0);
    else sub_tmp = tail;
    deallocate_term(sub);
    sub = sub_tmp;
  }

  if(sub && sub->get_size() == 1){
     mult1 = multiply_term(pivot, sub);
  } else if (sub && pivot->get_size() == 1) {
     mult1 = multiply_term(pivot, sub);
     mult3 = multiply_term(pivot,rem);
     larger_sub = 1;
  } else if (sub) {
    deallocate_term(sub);
    return -1;
  } else mult1 = pivot->copy();

  if(pivot->get_size() > 1){
    Term * old_mul = 0;
    while(old_mul != mult1){
      update_multv_remv_outerv(mult1->copy(), rem->copy(), outer_gc->get_lt(), target_proof);
      std::vector<Term*> rewritten = larger_pivot_rewriting(file, mult1, rem);
      if(rewritten.empty()) return 0;

      deallocate_term(rem);
      old_mul = mult1;
      mult1 = rewritten.front();
      rem = rewritten.back();
    }
    deallocate_term(old_mul);
  }


  if(rem) {
    mult2 = multiply_term(mult1, rem);
    deallocate_term(mult1);
  }  else mult2 = mult1;

  push_mstack_end(outer_gc->get_lm()->copy());
  if(rem != pivot){
    if(larger_sub){
      push_mstack_end(new Monomial(one, mult2));
      push_mstack_end(new Monomial(minus_one, mult3));
    } else {
      push_mstack_end(new Monomial(minus_one, mult2));
    }
    push_mstack_end(new Monomial(one, rem));
  }

  Polynomial * new_gc = build_poly();

  outer->delete_children();

  if(rem != pivot){
    while(mult2){
      Gate * n_child = gate(mult2->get_var_num());
      outer->children_push_back(n_child);
      n_child->parents_push_back(outer);
      mult2 = mult2->get_rest();
    }
  }



  delete(outer_gc);
  outer->set_gate_constraint(new_gc);
  if(proof) new_gc->set_idx(target_proof->get_idx());

  if(is_unit(outer)){
    outer->delete_children();
    eliminate_unit_gate(outer, file);
  }

  return 1;
}
/*-----------------------------------------------------------------------------*/
static void removing_f_chains(FILE * file) {
  msg("removing negative chains");

  bool change = 1, first = 1;
  while(change) {
    change = 0;
    for (auto i = carries.begin(); i != carries.end(); ++i) {

      Gate * outer = *i;
      if (outer->get_elim()) continue;
      if (outer->get_fsa() != 2) continue;
      if (outer->get_pp()) continue;
      if (outer == carry_in) continue;

      if (verbose > 1) {
        fputs("\n----- REWRITING -----\n\n", stdout);
        outer->get_gate_constraint()->print(stdout);
        fputs("\n",stdout);
      }

      Polynomial * outer_gc = outer->get_gate_constraint();
      if (outer_gc->get_size() != 2) continue;

      Term * outer_t = outer_gc->get_tail_term();



      if(first){
        init_gc.push_back(outer_gc->copy());

        if(outer_t->get_size() != outer_t->get_dual_count()){
          remove_positives_in_carry(outer, file);   // clean
          outer_gc = outer->get_gate_constraint();
          init_gc.push_back(outer_gc->copy());
          outer_t = outer_gc->get_tail_term();
        }
      }

      while(outer_t){
        outer_t = outer_t->get_rest();
      }
      outer_t = outer_gc->get_tail_term();

      int flag = 0;
      target_proof = outer->get_gate_constraint()->copy();

      if(outer_t->get_size() < 2) { msg("cannot calculate pivot of unit");
      } else if(outer_t->get_size() == 2) {

        if(!gate(outer_t->get_var_num())->get_xor_gate() &&
            outer_t->get_var()->is_dual()){
          Gate * outer_g = gate(outer_t->get_var_num());
          update_multv_remv_outerv(
            outer_g->get_gate_constraint()->get_tail_term(),
            outer_t->get_rest(), outer_gc->get_lt(), target_proof);

          eliminate_by_one_gate(outer, outer_g, file, 0);
        }

        flag = 1;
      } else {

        Gate * g0 = gate(outer_t->get_var_num());
        Gate * g1 = gate(outer_t->get_rest()->get_var_num());

        Polynomial * g0_gc = g0->get_gate_constraint();
        if (g0_gc->get_size() != 2) continue;

        Polynomial * g1_gc = g1->get_gate_constraint();
        if (g1_gc->get_size() != 2) continue;

        Term * t0 = g0_gc->get_tail_term();
        Term * t1 = g1_gc->get_tail_term();

        while(t0->get_size() < t1->get_size()){

          expand_tail_term_and_update_gc(g0, file);
        //  die("here");
          t0 = g0->get_gate_constraint()->get_tail_term();
        }

        Term * pivot =  calc_pivot(t0, t1);
        if(!pivot) continue;

        flag = pivot_rewriting(outer, pivot, file);
        if (flag == -1) expand_first_two(outer_t, file);

        deallocate_term(pivot);
      }

      if (flag == 1) {
        add_to_resolved(outer);
        carries.erase(i--);
        change = 1;
      }

      if(verbose > 1 && !outer->get_elim())
        outer->get_gate_constraint()->print(stdout);

    }

    if(first && !carries.empty()) {
      std::reverse(carries.begin(), carries.end());
      first = 0;
    }
  }

  for(auto it = init_gc.begin(); it!= init_gc.end(); ++it){
    Polynomial * p = *it;
    delete(p);
  }
}

/*============================================================================*/

void dual_preprocessing(FILE * file){
    remove_only_positives(file);
    backward_substitution(file);
    removing_f_chains(file);
    clear_resolved_gc();
}
