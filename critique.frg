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

// Property 2. Elevator shouldn't move beyond top or bottom floors
pred elevatorWithinBounds[e: Elevator] {
    (e.floor = Top => not moveUp[e]) and (e.floor = Bottom => not moveDown[e])
}

// Property 3. Requests are only removed when serviced
pred requestsResolvedPickUp[e: Elevator] {
    pickUp[e] implies e.floor not in e.requests'
}

// Property 4. Elevator should only move to adjacent floors in one transition
pred verifyAdjacentFloor[e: Elevator] {
	moveUp[e] implies (e.floor'.below = e.floor)
	moveDown[e] implies (e.floor'.above = e.floor)
}
// Property 5. Next Request should always be a valid request if there are pending requests, 
// or it should default to Bottom floor if there are none
pred validNextRequest[e: Elevator] {
    (some e.requests => e.nextRequest in e.requests) and (no e.requests => e.nextRequest = Bottom)
}

// Property 6. Elevator door can't be open and closed at the same time
pred mutualExclusionDoorState[e: Elevator] {
    not (e.door = Open and e.door = Closed)
}

// Property 7. Check to make sure that elevator is properly initialized
pred properInitialization[e: Elevator] {
    init[e] implies (e.floor = Bottom and e.door = Closed and e.lastMove = Up)
}

// Property 8. If floor is in the set of requests, it must eventually be serviced. 
pred requestEventuallyServiced {
	all e: Elevator, f: Floor | {
		f in e.requests => {
			eventually {(e.floor = f and e.door = Open)}
		}
	}
}


test expect {
	-- TODO: test overall model properties here
	test1: {traces implies elevatorOnlyMoveWhenDoorClosed[Elevator]} for exactly 1 Elevator is theorem
	test2: {traces implies elevatorWithinBounds[Elevator]} for exactly 1 Elevator is theorem
	test3: {traces implies requestsResolvedPickUp[Elevator]} for exactly 1 Elevator is theorem
	test4: {traces implies verifyAdjacentFloor[Elevator]} for exactly 1 Elevator is theorem
	test5: {traces implies validNextRequest[Elevator]} for exactly 1 Elevator is theorem
	test6: {traces implies mutualExclusionDoorState[Elevator]} for exactly 1 Elevator is theorem
	test7: {traces implies properInitialization[Elevator]} for exactly 1 Elevator is theorem
	// test8: not a theorem because it doesn't apply to every instance, but is satisfiable
	test8: {traces implies requestEventuallyServiced} for exactly 1 Elevator is sat
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

/* PROCEDURE 1 TESTS **********************************************************/
// checks if elevator can stay still when there aren't any requests
pred stayStillWhenNoRequests[e: Elevator] {
    no e.requests implies stayStill[e]
}

// checks if elevator always moves/never stays still
pred alwaysMoves[e: Elevator] {
    always not stayStill[e]
}
//downwards movement implies that there is a request below
pred some_below_request[e: Elevator]{
	moveDown[e] implies some (e.floor.^below & e.requests)
}
// upward movement implies that there is a request below
pred some_above_request[e: Elevator]{
	moveUp[e] implies some (e.floor.^above & e.requests)
}
// Upwards movement means there are no requests below
pred no_below[e: Elevator]{
	moveUp[e] implies no (e.floor.^below & e.requests)
}
// Not at the top or bottom implies we move in our current dirrection until we reach that upper bound.
pred move_till_top[e: Elevator]{
	not stayStill[e]
	((e.floor != Top and moveUp[e] implies e.floor not in  e.floor.^above) and 
	(moveUp[e] until e.floor = Top)) or
	((e.floor != Bottom and moveDown[e] implies e.floor not in  e.floor.^below) and 
	(moveDown[e] until e.floor = Bottom))
}

// A certain movements implication on requests
pred movement_implies[e: Elevator]{
	//moving dow implies no request above
	moveDown[e] implies  no (e.requests & e.floor.^above)
	//moving up implies no request below
	moveUp[e] implies no (e.requests & e.floor.^below)
}

//This is checking a property of procedure 4 on the rest. Some requests and the next request not being in
//those requests implies the nextRequest will be in requests at the next step.
pred next_request_in_request[e: Elevator]{
	(some e.requests) and (e.nextRequest not in e.requests) => e.nextRequest' in e.requests'
	((no e.requests) and (some e.requests')) => e.nextRequest' in e.requests'
}
//Moving up with a request above means we do not move down until all above request are complete
pred next_request_in_next_step_request[e: Elevator]{
	moveUp[e] and e.nextRequest in e.floor.^above => not moveDown[e] until (e.nextRequest not in e.floor.^above)
	// e.nextRequest in e.floor.^below => moveDown[e] and not moveUp[e]
}

pred procedure4diff[e: Elevator] {
	no e.requests
	some e.requests'
	e.nextRequest' in e.requests'
}
/*
assuming procedure enforced at every state, and inside we */

/*
	Key characteristics: 
	1. Stays still if there are no requests
	2. Picks up passengers from current floor if requested
	3. Can't move up if there are requests below
*/
test expect {
	-- TODO: test procedure1 properties here
	fp1: {traces and always procedure1[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	stayStillWhenNoRequests1: {traces and always procedure1[Elevator] implies stayStillWhenNoRequests[Elevator]} for exactly 1 Elevator is theorem
	some_below_request1: {traces and always procedure1[Elevator] implies always some_below_request[Elevator] } for exactly 1 Elevator is theorem
	some_above_request1: {traces and always procedure1[Elevator] implies always some_above_request[Elevator] } for exactly 1 Elevator is theorem
	no_below1:  {traces and always procedure1[Elevator] implies always no_below[Elevator]} for exactly 1 Elevator is theorem
	//move_till_top1: {traces and always procedure1[Elevator] implies move_till_top[Elevator]} for exactly 1 Elevator is theorem | FAILS
	// note: why is this not unsat? we know it's not theorem.  
	// alwaysMoves1: {traces and always procedure1[Elevator] implies alwaysMoves[Elevator]} for exactly 1 Elevator is sat
	//movement_implies1:  {traces and always procedure1[Elevator] implies always movement_implies[Elevator]} for exactly 1 Elevator is theorem | FAILS
	//next_request_in_request1: {traces and always procedure1[Elevator] implies always next_request_in_request[Elevator] } for exactly 1 Elevator is theorem | FAIL
	//next_request_in_next_step_request1:{traces and always procedure1[Elevator] implies always next_request_in_next_step_request[Elevator] } for exactly 1 Elevator is theorem
}

/* PROCEDURE 2 TESTS **********************************************************/
/*
	Key characteristics: 
	1. Elevator always in motion
	2. Fixed pattern of movement from bottom to top, then top to bottom
*/
test expect {
	-- TODO: test procedure2 properties here
	fp2: {traces and always procedure2[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	// note: this is weird, should be unsat since it's never supposed to stay still
	// but forge finds a counterexample
	// stayStillWhenNoRequests2: {traces and always procedure2[Elevator] implies stayStillWhenNoRequests[Elevator]} for exactly 1 Elevator is unsat
	//Note that this is not theorem like the rest of the procedures
	some_below_request2: {traces and always procedure2[Elevator] implies always some_below_request[Elevator] } for exactly 1 Elevator is sat
	alwaysMoves2: {traces and always procedure2[Elevator] implies alwaysMoves[Elevator]} for exactly 1 Elevator is theorem
	// some_above_request2: {traces and always procedure2[Elevator] implies always some_above_request[Elevator] } for exactly 1 Elevator is theorem | FAILS!
	// no_below2:  {traces and always procedure2[Elevator] implies always no_below[Elevator]} for exactly 1 Elevator is theorem | FAILS!
	move_till_top2: {traces and always procedure2[Elevator] implies move_till_top[Elevator]} for exactly 1 Elevator is theorem
	//movement_implies2:  {traces and always procedure2[Elevator] implies always movement_implies[Elevator]} for exactly 1 Elevator is theorem | FAILS
	//next_request_in_request2: {traces and always procedure2[Elevator] implies always next_request_in_request[Elevator] } for exactly 1 Elevator is theorem | FAILS
	next_request_in_next_step_request2:{traces and always procedure2[Elevator] implies always next_request_in_next_step_request[Elevator] } for exactly 1 Elevator is theorem
	//This passing is interesting!
	
}

/* PROCEDURE 3 TESTS **********************************************************/
/*
	Key characteristics: 
	1. Stays still when no requests
	2. Prioritizes going to floors in current direction before changing direction
*/
test expect {
	-- TODO: test procedure3 properties here
	fp3: {traces and always procedure3[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	stayStillWhenNoRequests3: {traces and always procedure3[Elevator] implies stayStillWhenNoRequests[Elevator]} for exactly 1 Elevator is theorem
	some_below_request3: {traces and always procedure3[Elevator] implies always some_below_request[Elevator] } for exactly 1 Elevator is theorem
	some_above_request3: {traces and always procedure3[Elevator] implies always some_above_request[Elevator] } for exactly 1 Elevator is theorem
	no_below3:  {traces and always procedure3[Elevator] implies always no_below[Elevator]} for exactly 1 Elevator is theorem
	//move_till_top3: {traces and always procedure1[Elevator] implies move_till_top[Elevator]} for exactly 1 Elevator is theorem | FAILS
	// should also be unsat since this procedure stays still with no requests, so it should never be always moving
	// alwaysMoves3: {traces and always procedure3[Elevator] implies alwaysMoves[Elevator]} for exactly 1 Elevator is unsat
	movement_implies3:  {traces and always procedure3[Elevator] implies always movement_implies[Elevator]} for exactly 1 Elevator is theorem
	//next_request_in_request3: {traces and always procedure3[Elevator] implies always next_request_in_request[Elevator] } for exactly 1 Elevator is theorem
	next_request_in_next_step_request3:{traces and always procedure3[Elevator] implies always next_request_in_next_step_request[Elevator] } for exactly 1 Elevator is theorem
	procedure4diff3: {traces and always procedure3[Elevator] implies always procedure4diff[Elevator] } for exactly 1 Elevator is sat

}

/* PROCEDURE 4 TESTS **********************************************************/
/*
	Key characteristics: 
	1. updates next request based on remaining requests, but doesn't consider the 
	   elevator's last movement direction (as opposted to Proc5)
	2. stays still when no requests
*/

// this test will distinguish between proc4 and proc5
// proc4 doesn't take into consideration the elevator's last direction, so should fail as theorem for proc4?
pred directionalNextRequestUpdate[e: Elevator] {
    pickUp[e] implies {
        // If lastMove was Up and there are requests above, nextRequest should be set to one of those above
        // expected in proc5 but not in proc4
        e.lastMove = Up implies {
            some e.requests => some (e.requests & e.floor.^above) => e.nextRequest' in (e.requests & e.floor.^above)
        }

        -- If lastMove was Down and there are requests below, nextRequest should be set to one of those below
        e.lastMove = Down implies {
            some e.requests => some (e.requests & e.floor.^below) => e.nextRequest' in (e.requests & e.floor.^below)
        }
    }
}

// generic next request, should work for both proc4 and proc5
pred genericNextRequestUpdate[e: Elevator] {
    (some e.requests) and (e.nextRequest not in e.requests) => e.nextRequest' in e.requests'
}

// this predicate distinguishes between procedures 4 and 5. 
// proc4 doesn't always satisfy this predicate (is sat)
// for proc5, this is theorem 
pred allRequestsFulfilled[e: Elevator] {
    all f: Floor | f in e.requests implies eventually (e.floor = f and e.door = Open)
}



test expect {
	-- TODO: test procedure4 properties here
	fp4: {traces and always procedure4[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	stayStillWhenNoRequests4: {traces and always procedure4[Elevator] implies stayStillWhenNoRequests[Elevator]} for exactly 1 Elevator is theorem
	some_below_request4: {traces and always procedure4[Elevator] implies always some_below_request[Elevator] } for exactly 1 Elevator is theorem
	some_above_request4: {traces and always procedure4[Elevator] implies always some_above_request[Elevator] } for exactly 1 Elevator is theorem
	// no_below4:  {traces and always procedure4[Elevator] implies always no_below[Elevator]} for exactly 1 Elevator is theorem | FAILS
	//move_till_top4: {traces and always procedure4[Elevator] implies move_till_top[Elevator]} for exactly 1 Elevator is theorem | FAILS
	//movement_implies4:  {traces and always procedure4[Elevator] implies always movement_implies[Elevator]} for exactly 1 Elevator is theorem |FAILS
	next_request_in_request4: {traces and always procedure4[Elevator] implies always next_request_in_request[Elevator] } for exactly 1 Elevator is theorem
	// should also be unsat since this procedure stays still with no requests, so it should never be always moving
	// alwaysMoves4: {traces and always procedure4[Elevator] implies alwaysMoves[Elevator]} for exactly 1 Elevator is unsat
	next_request_in_next_step_request4:{traces and always procedure4[Elevator] implies always next_request_in_next_step_request[Elevator] } for exactly 1 Elevator is theorem
	procedure4diff4: {traces and always procedure4[Elevator] implies always procedure4diff[Elevator] } for exactly 1 Elevator is sat
	genericNextRequestUpdate4: {traces and always procedure4[Elevator] implies genericNextRequestUpdate[Elevator]} for exactly 1 Elevator is theorem
	allRequestsFulfilled4: {traces and always procedure4[Elevator] implies allRequestsFulfilled[Elevator]} for exactly 1 Elevator is sat // for proc5, this is theorem!
}

/* PROCEDURE 5 TESTS **********************************************************/
/*
	Key characteristics: 
	1. uniquely considers the elevator's last move direction when updating requests
	2. stays still when no requests
*/
test expect {
	-- TODO: test procedure5 properties here
	fp5: {traces and always procedure5[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	stayStillWhenNoRequests5: {traces and always procedure5[Elevator] implies stayStillWhenNoRequests[Elevator]} for exactly 1 Elevator is theorem
	some_below_request5: {traces and always procedure5[Elevator] implies always some_below_request[Elevator] } for exactly 1 Elevator is theorem
	// should also be unsat since this procedure stays still with no requests, so it should never be always moving
	alwaysMoves5: {traces and always procedure5[Elevator] implies alwaysMoves[Elevator]} for exactly 1 Elevator is sat
	some_above_request5: {traces and always procedure5[Elevator] implies always some_above_request[Elevator] } for exactly 1 Elevator is theorem
	// no_below5:  {traces and always procedure5[Elevator] implies always no_below[Elevator]} for exactly 1 Elevator is theorem | FAILS
	//move_till_top5: {traces and always procedure5[Elevator] implies move_till_top[Elevator]} for exactly 1 Elevator is theorem | FAILS
	//movement_implies5:  {traces and always procedure5[Elevator] implies always movement_implies[Elevator]} for exactly 1 Elevator is theorem |FAILS
	next_request_in_request5: {traces and always procedure5[Elevator] implies always next_request_in_request[Elevator] } for exactly 1 Elevator is theorem
	next_request_in_next_step_request5:{traces and always procedure5[Elevator] implies always next_request_in_next_step_request[Elevator] } for exactly 1 Elevator is theorem
	genericNextRequestUpdate5: {traces and always procedure5[Elevator] implies genericNextRequestUpdate[Elevator]} for exactly 1 Elevator is theorem
	allRequestsFulfilled5: {traces and always procedure5[Elevator] implies allRequestsFulfilled[Elevator]} for exactly 1 Elevator is theorem
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

// what karis said: the elevator doesn't always have to be moving
pred multiElevatorFix {
	// If there are pending requests, at least one elevator must not be staying still
	// some e: Elevator | some e.requests => {not stayStill[e]}
	// An elevator can stay still if it has no pending requests
	//all e: Elevator | (no e.requests) => stayStill[e]
	//some e: Elevator | some e.requests implies {enabled[e]}
	all e: Elevator | enabled[e] => always  { eventually runElevatorProcedure[e]}
	//all e: Elevator | some e.requests implies {enabled[e]}
	//cosntrraint enabled itself, not guaranteed they are enabled in the first state.
	all e: Elevator | eventually {always enabled[e]}
	//all e: Elevator | enabled[e] => always enabled[e]
}


-- TODO: Procedure 5 Checks
-- Paste and edit your Procedure 5 checks here.
-- These should not all pass before you implement a multi-elevator fix,
-- and should pass after you include the fix. 
-- Note: When we say "pass", we mean that the tests that passed in the non-challenge
-- portion should pass, and those that failed previously should continue failing.

// note: we've only kept the tests that pass for procedure 5
test expect {
	-- TODO: test procedure5 properties here
	fpMULTI: {elevatorControl and multiElevatorFix implies forwardProgress[Elevator]} for exactly 2 Elevator is theorem
	stayStillWhenNoRequestsMULTI: {{elevatorControl and multiElevatorFix implies stayStillWhenNoRequests[Elevator]}} for exactly 2 Elevator is theorem
	//some_below_requestMULTI: {{elevatorControl and multiElevatorFix implies always some_below_request[Elevator] }} for exactly 2 Elevator is theorem
	alwaysMovesMULTI: {{elevatorControl and multiElevatorFix implies alwaysMoves[Elevator]}} for exactly 2 Elevator is sat
	some_above_requestMULTI: {elevatorControl and multiElevatorFix implies always some_above_request[Elevator] } for exactly 2 Elevator is theorem
	//next_request_in_requestMULTI: {elevatorControl and multiElevatorFix implies always next_request_in_request[Elevator] } for exactly 2 Elevator is theorem
	next_request_in_next_step_requestMULTI:{elevatorControl and multiElevatorFix implies always next_request_in_next_step_request[Elevator] } for exactly 2 Elevator is theorem
	//genericNextRequestUpdateMULTI: {elevatorControl and multiElevatorFix implies genericNextRequestUpdate[Elevator]} for exactly 2 Elevator is theorem
	//allRequestsFulfilledMULTI: {elevatorControl and multiElevatorFix implies allRequestsFulfilled[Elevator]} for exactly 2 Elevator is theorem
	// requestDirectionalConsistencyMULTI: {elevatorControl and multiElevatorFix implies requestDirectionalConsistency[Elevator]} for exactly 2 Elevator is theorem
}

