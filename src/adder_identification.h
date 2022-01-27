/*------------------------------------------------------------------------*/
/* TeluMA2 : AIG Multiplier Verification Tool.
 *
 * Copyright(C) 2021 Daniela Kaufmann, Johannes Kepler University Linz
 *
 * adder_identification.h: functions used for identifying final stage adder
 */
/*------------------------------------------------------------------------*/
#ifndef AMULET2_SRC_ADD_IDENTIFICATION_H_
#define AMULET2_SRC_ADD_IDENTIFICATION_H_
/*------------------------------------------------------------------------*/
#include <vector>

#include "gate.h"
/*------------------------------------------------------------------------*/
extern Gate * carry_in;

extern std::vector<Gate*> carries;
/*------------------------------------------------------------------------*/

/**
    Routine for identifying the final stage adder

    @return True if all checks succeeded
*/
bool identify_final_stage_adder();

/*------------------------------------------------------------------------*/

#endif  // AMULET2_SRC_ADD_IDENTIFICATION_H_
