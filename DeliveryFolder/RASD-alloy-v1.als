// Signature definitions

abstract sig User {}
sig Company extends User {}
sig Student extends User {}

enum Boolean {TRUE, FALSE}
enum InterviewState {
	SCHEDULED,
	CONFIRMED, 
	ONGOING, 
	CLOSED, 
	CANCELLED
}

sig Slot {
	interviews: set Interview // Set of interviews that *could* be held in this slot
}

sig Internship {
	company: one Company
}

sig Interview {
	internship: one Internship,
	student: one Student,
	var state: one InterviewState,
	var veredictApproved: lone Boolean,
	var scheduledTime: lone Slot // Slot in which the interview is confirmed
}

// Predicates

pred createInterview(interview: Interview) {
    interview.state = SCHEDULED
}

pred studentAcceptInvite(interview: Interview, slot: Slot) {
	interview.state = SCHEDULED
	after {
		interview.state' = CONFIRMED
		interview.scheduledTime' = slot
		slot.interviews' = {interview}
	}	
}

pred studentDeclineInvite(interview: Interview) {
        interview.state = SCHEDULED
        after {interview.state' = CANCELLED}
}

pred startInterview(interview: Interview) {
        interview.state = CONFIRMED
        after {interview.state' = ONGOING}
}

pred closeInterview(interview: Interview, approved: Boolean) {
        interview.state = ONGOING
        after {
		interview.state' = CLOSED
        	interview.veredictApproved' = approved
	}
}

pred cancelInterview(interview: Interview) {
        interview.state = SCHEDULED
        after {interview.state' = CANCELLED}
}

pred doNothing {}

// Facts

fact systemBehavior {
	all interview: Interview | once interview.state = SCHEDULED
	always (
		some i: Interview | (
			createInterview[i] or
			(some s: Slot | studentAcceptInvite[i, s]) or
			studentDeclineInvite[i] or
			startInterview[i] or
			cancelInterview[i] or
			(some b: Boolean | closeInterview[i, b])) or
			doNothing
	)
}

fact stateTransitions {
    always all i: Interview {
        // Transition from SCHEDULED
        (i.state = SCHEDULED implies after i.state' in CONFIRMED + CANCELLED) 
        
        // Transition from CONFIRMED
        (i.state = CONFIRMED implies after i.state' = ONGOING)
        
        // Transition from ONGOING
        (i.state = ONGOING implies after i.state' = CLOSED)
        
        // CLOSED and CANCELLED are terminal states
        (i.state = CLOSED implies after always i.state = CLOSED)
        (i.state = CANCELLED implies after always i.state = CANCELLED)
    }
}



fact closedIffVeredict {
    all interview: Interview |
	always (
		(interview.state = CLOSED implies some interview.veredictApproved) &&
		(some interview.veredictApproved implies interview.state = CLOSED))
}

fact scheduledTimeImpliesState {
   all interview: Interview |
	always ((some interview.scheduledTime implies interview.state in 
			CONFIRMED +
			ONGOING +
			CLOSED
		) &&
		(interview.state in CONFIRMED + ONGOING +CLOSED implies some interview.scheduledTime))
}

fact symetricalSlot {
   all interview: Interview |
	always (some interview.scheduledTime implies interview.scheduledTime.interviews = {interview})
}

fact uniqueStudentInterviewPerInternship {
    all s: Student, i: Internship |
        always (lone interview: Interview | 
            interview.student = s and interview.internship = i)
}

// Output model
pred show {}
run studentAcceptInvite for 3 but 10 steps

