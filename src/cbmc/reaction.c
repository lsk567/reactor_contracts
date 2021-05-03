#include <stdio.h>
#include <stdbool.h>


bool s;
void reaction_door(bool _in_value){
	__CPROVER_assume(true);
	s = _in_value;
	__CPROVER_assert(s == _in_value, "G3");
}

bool controller_out;
void reaction_controller(){
	__CPROVER_assume(true);
	bool v = true;
	controller_out = v;
	__CPROVER_assert(controller_out == v, "G2");
}

bool vision_out;
bool vision_ramp_exists;
void reaction_vision(bool _in_value){
	__CPROVER_assume(true);
	if(vision_ramp_exists){
		vision_out = _in_value;
	}
	__CPROVER_assert(!(vision_ramp_exists == true) || 
			   vision_out == _in_value, "G4");
}
