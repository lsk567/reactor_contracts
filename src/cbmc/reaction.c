#include <stdio.h>
#include <stdbool.h>


// reaction door
bool s;
void reaction_door(bool _in_value){
	__CPROVER_assume(true);
	s = _in_value;
	__CPROVER_assert(s == _in_value, "G3");
	__CPROVER_assert(s == true, "G3 wrong");
	
}



bool controller_out;
void reaction_controller(){
	__CPROVER_assume(true);
	bool v = true;
	controller_out = v;
	__CPROVER_assert(controller_out == v, "G2");
	__CPROVER_assert(controller_out == false, "G2 wrong");
}

//reaction vision

bool vision_out;
bool vision_ramp_exists;
void reaction_vision(bool _in_value){
	__CPROVER_assume(true);
	if(vision_ramp_exists){
		vision_out = _in_value;
	}
	__CPROVER_assert(!(vision_ramp_exists == true) || vision_out == _in_value, "G4");
	__CPROVER_assert(vision_out == _in_value, "G4_wrong");// incorrect contract
}
