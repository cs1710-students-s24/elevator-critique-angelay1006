#lang forge/temporal
-- Import all the elevator procedures to critique, along with
--   all of the sigs and predicates:
open "elevator.frg"


/*------------------------------------*\
|    Elevator Procedure Descriptions   |
\*------------------------------------*/

-- We provide the source code for 5 different procedures in elevator.frg. 
--   Based on the code and its comments, what documentation do you think would best describe each procedure? 
--   Think about the differences between the procedures and how to best communicate them. 

-- Procedure 1:
--   TODO:
/* 
	This procedure makes the elevator remain on the same floor if there are no pending requests, 
	which also implies that it should always be moving if there's at least one request. If 
	the current floor has pending requests, the elevator must always pick up passengers. 
	The movement of the elevator is also enforced: the elevator shouldn't move up if there are floors 
	below its current position, and it shouldn't move down if there are no requests from floors below. 
	The order of getting to requests is therefore bottom to top. 
*/


-- Procedure 2:
--   TODO:  
/* 
	This procedure enforces that the elevator must always be moving and that
	if there's a request from a certain floor, the elevator has to do the pickup operation. 
	The elevator cycles between the top and bottom floors by moving up from the bottom till
	it reaches the top and moving down from the top till it reaches the bottom,
	without any stops. 
*/

-- Procedure 3:
--   TODO: 
/* 
	This procedure makes the elevator stay on the same floor if there are no requests, 
	and always pick up passengers on the current floor if there's a request. It also
	enforces that the elevator does pickups more efficiently: it shouldn't change 
	direction until all requests in its movement path (up or down) are completed. For 
	example, if the elevator is already moving up, then it has to service all requested 
	floor above the one it's currently on before being able to move down. 
*/

-- Procedure 4:
--   TODO: 
/*
	Similarly to Procedure 3, the elevator stays on the same floor if there are no requests,
	and will always pick up passengers from the current floor if requested. The elevator's
	movement is directed towards the floor that is currently the next request, and won't
	move in the direction opposite to this target. This procedure also updates when
	the current next request is fulfilled or when new requests are made. 
*/

-- Procedure 5:
--   TODO: 
/*
	Procedure 5 stays on the same floor if there are no requests, and will always pick up 
	passengers from the current floor if requested. The movement of the elevator will 
	match the relative location of the next requested location: when the current floor
	satisfies the next request, the next destination will be updated based on the elevator's 
	last movement direction so it won't travel unnecessarily. For example, if the elevator's
	last movement direction was upwards and there are requests from floors above, the 
	next request would be updated to one of those requests, continuing an upward movement.
*/


/*------------------------------------*\
|    Model Properties + Verification   |
\*------------------------------------*/

-- TODO: encode a few predicates to test the properties of the overall model
--   and verify whether or not they hold in the following test-expect block

-- Hint: Think about what should / should not be possible for a typical elevator!

// Property: Movement is only possible when the elevator's door is closed
pred elevatorOnlyMoveWhenDoorClosed[e: Elevator] {
	e.floor != e.floor' => e.door = Closed
}

test expect {
	-- TODO: test overall model properties here
	test1: {traces implies elevatorOnlyMoveWhenDoorClosed[Elevator]} for exactly 1 Elevator is theorem
	
}


/*-------------------------------------------------*\
|    Elevator Procedure Properties + Verification   |
\*-------------------------------------------------*/

-- TODO: encode a few predicates to test the properties of the 5 elevator procedures
--   and verify whether or not they hold in the following test-expect blocks. Remember
--   that procedures 4 and 5 make use of the `nextRequest` and `lastMove` Elevator
--   fields, so be sure to write predicates that test properties of these fields too.

-- Hint: Think about what behavior is allowed / expected by each procedure!

// Property: forward progress is always possible
//  Hint: `enabled` does not enforce that forward progress *happens* – just that it's possible.
pred forwardProgress[e: Elevator] {
	always eventually enabled[e]
}


test expect {
	-- TODO: test procedure1 properties here
	fp1: {traces and always procedure1[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	-- TODO: test procedure2 properties here
	fp2: {traces and always procedure2[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	-- TODO: test procedure3 properties here
	fp3: {traces and always procedure3[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
}

test expect {
	-- TODO: test procedure4 properties here
	fp4: {traces and always procedure4[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	-- TODO: test procedure5 properties here
	fp5: {traces and always procedure5[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem

}


/*-------------------------------------*\
|    Challenge Problem: Two Elevators   |
\*-------------------------------------*/

-- This predicate is meant to help test various procedures:
--   just change which procedure is being called here (in one place)
--   and the controller will follow suit.
-- You should focus on Procedure 5, but we have provided this in case you want
-- to try out the other procedures with multiple elevators!
pred runElevatorProcedure[e: Elevator] {
	procedure5[e]
}

-- The controller, depending on its own needs (which are incomprehensible to
--   mortals and people who work in the CIT) will allow some elevator(s) to go
--   in every state (but not necessarily all of them).
-- This predicate is needed for the challenge problem, but not sooner. 
pred elevatorControl {
	traces
	always {some e: Elevator | runElevatorProcedure[e]}
    always {all e: Elevator | not runElevatorProcedure[e] => stayStill[e]}
}

-- TODO: Multi-Elevator Fix
-- Add a constraint that ensures procedures work for multiple elevators. 



-- TODO: Procedure 5 Checks
-- Paste and edit your Procedure 5 checks here.
-- These should not all pass before you implement a multi-elevator fix,
-- and should pass after you include the fix. 
-- Note: When we say "pass", we mean that the tests that passed in the non-challenge
-- portion should pass, and those that failed previously should continue failing.
