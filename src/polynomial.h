/*------------------------------------------------------------------------*/
/*! \file polynomial.h
    \brief contains arithmetic operations for polynomials

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#ifndef AMULET2_SRC_POLYNOMIAL_H_
#define AMULET2_SRC_POLYNOMIAL_H_
/*------------------------------------------------------------------------*/
#include <list>
#include <deque>
#include <cstring>

#include "monomial.h"
/*------------------------------------------------------------------------*/

/** \class Polynomial
    This class is used to polynomials.
*/
class Polynomial {
  int idx;  // /< index as used in pac proofs

  int level = 1;  // /< level of polynomials needed for certificates

  std::deque<Monomial*> mon;  // /< sorted deque of monomials

 public:
  /** Constructor */
  Polynomial();

  /** Constructor

     @param _idx default for index is zero

  */
  explicit Polynomial(int _idx);

  /** Getter for member idx

      @return integer
  */
  int get_idx() const {return idx;}

  /**
      Setter for idx

      @param idx_ integer
  */
  void set_idx(int idx_) {idx = idx_;}

  /** Getter for member level

      @return integer
  */
  int get_level() const {return level;}

  /**
      Setter for level

      @param level_ integer
  */
  void set_level(int level_) {level = level_;}

  /**
      Getter for size

      @return size_t
  */
  size_t get_size() const {return mon.size();}

  /**
      Getter for mon

      @return std::deque<Monomial*>
  */
  std::deque<Monomial*> get_mon() const {return mon;}

  /**
      Getter for begin of mon

      @return std::deque<Monomial*>::const_iterator
  */
  std::deque<Monomial*>::const_iterator mon_begin() const {return mon.begin();}

  /**
      Getter for end of mon

      @return std::deque<Monomial*>::const_iterator
  */
  std::deque<Monomial*>::const_iterator mon_end() const {return mon.end();}

  /**
      Appends monomial m to mon

      @param m Monomial*
  */
  void mon_push_back(Monomial * m) {mon.push_back(m);}

  /** Returns the leading term

      @return Term*
  */
  Term * get_lt() const {return mon.front()->get_term();}
  Monomial * get_lm() const {return mon.front();}


  Monomial * get_tail_mon () const { return mon.back();}
  Term * get_tail_term () const { return mon.back()->get_term();}

  /**
      Copy routine

      @return A hard copy of the current polynomial
  */
  Polynomial * copy() const;

  /**
      Printing routine

      @param file Output file
      @param end if true we print trailing ";"
  */
  void print(FILE * file, bool end = 1) const;

  /** Destructor */
  ~Polynomial();


  /**
      Returns whether the polynomial is the constant zero polynomial

      @return bool
  */
  bool is_constant_zero_poly() const;

  /**
      Returns whether the polynomial is the constant one polynomial

      @return bool
  */
  bool is_constant_one_poly() const;

  /**
      Returns whether the polynomial contains dual var

      @return bool
  */
  bool contains_dual_var() const;

  /**
      Returns the size of the smallest term

      @return integer
  */
  int min_term_size() const;
};
/*------------------------------------------------------------------------*/
// Polynomials are generated using a sorted array "mstack"

/**
    Enlarges the allocated size of mstack
*/
void enlarge_mstack();

/**
    Sets the number of elements in the stack to 0
*/
void clear_mstack();

/**
    Deallocates mstack
*/
void deallocate_mstack();

/**
    Checks whether mstack is empty

    @return true if mstack is empty
*/
bool mstack_is_empty();

/**
    Pushes a monomial to the end of the stack

    @param t monomial to be added to the mstack
*/
void push_mstack_end(Monomial *t);

/**
    Pushes a monomial to the stack such that mstack remains sorted

    @param t monomial to be added to the mstack
*/
void push_mstack(Monomial *t);


/**
    Generates a polynomial from mstack and clears mstack

    @return Polynomial*
*/
Polynomial * build_poly(bool need_sorting = 0 );


/*------------------------------------------------------------------------*/

/**
    Add two polynomials p1+p2

    @param p1 Polynomial*
    @param p2 Polynomial*

    @return Polynomial*, sum of p1+p2
*/
Polynomial * add_poly(const Polynomial *p1, const Polynomial *p2);

/**
    Multiplies two polynomials p1*p2

    @param p1 Polynomial*
    @param p2 Polynomial*

    @return Polynomial*, product of p1*p2
*/
Polynomial * multiply_poly(const Polynomial *p1, const Polynomial *p2, bool dual_cut = 1);


Polynomial * multiply_poly_with_term(const Polynomial *p1, Term * t);
/**
    Multiplies a polynomial p1 with a constant c

    @param p1: Polynomial*
    @param c:  mpz_t object

    @return Polynomial*, product of c*p1
*/
Polynomial * multiply_poly_with_constant(const Polynomial *p1, mpz_t c);


/**
    Returns the quotient of dividing a polynomial p1 by a term t

    @param p1 Polynomial*
    @param t  Term *

    @return Polynomial defining the quotient of p1/t
*/
Polynomial * divide_by_term(const Polynomial * p1, const Term * t);

/**
    Appends p2 to p1

    @param p1 Polynomial*
    @param p2 Polynomial*

    @return Polynomial*, [p1, p2]
*/
void link_poly(Polynomial *p1, const Polynomial *p2);

Polynomial * build_one_minus_x_times_y_poly(Term * x, Term *y);

/*---------------------------------------------------------------------------*/
// / gmp for 1
extern mpz_t one;

// / gmp for -1
extern mpz_t minus_one;

// / gmp for 2
extern mpz_t base;

// / gmp for 2^NN
extern mpz_t mod_coeff;
/*---------------------------------------------------------------------------*/
/**
    Initializes all global gmp objects

    @param exp unsigned exponent for mod coeff
*/
void init_mpz(unsigned exp);

/**
    Clears all globally allocated gmp objects
*/
void clear_mpz();

#endif  // AMULET2_SRC_POLYNOMIAL_H_
