/*------------------------------------------------------------------------*/
/*! \file variable.h
    \brief contains the class Var

  Part of TeluMA : AIG Multiplier Verification Tool.
  Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
*/
/*------------------------------------------------------------------------*/
#ifndef AMULET2_SRC_VARIABLE_H_
#define AMULET2_SRC_VARIABLE_H_
/*------------------------------------------------------------------------*/
#include <string>

#include "hash_val.h"
/*------------------------------------------------------------------------*/

/** \class Var
    represents a variable is assigned to a gate(see <gate.h>) and is
    used to represent variables in terms, see <term.h>
*/

class Var {
    // / name of variable
    const std::string name;

    // / Hash value of variables, used for storing terms
    int hash;

    // / Increasing value that indicates the order of the variable
    const int level;

    // / corresponding value used to relate AIG gates to Gate class
    const int num;

    // / links dual variable
    const Var * dual;

    bool d = 0;

 public:
  /** Constructor

     @param name_ name
     @param level_ level
     @param num_ num, default is 0

  */
  Var(std::string name_, int level_, int num_ = 0, bool dual_ = 0):
     name(name_),  level(level_), num(num_), d(dual_) {
       hash = hash_string(name_);

     }

   /** Getter for member name, and converts string to char*

       @return const char *
   */
  const char * get_name() const {return name.c_str();}

  /** Getter for member is_dual

      @return bool
  */
  bool is_dual() const {return d;}

  /** Getter for member hash

      @return integer
  */
  int get_hash() const {return hash;}

  /** Getter for member level

      @return integer
  */
  int get_level() const {return level;}

  /** Getter for member num

      @return integer
  */
  int get_num() const {return num;}

  /** Getter for member dual

    @return integer
  */
  const Var * get_dual() const {return dual;}

  /** Setter for dual varialbe
      @param d Variable *
  */
  void set_dual_var(const Var *d) { dual = d;}
};


#endif  // AMULET2_SRC_VARIABLE_H_
