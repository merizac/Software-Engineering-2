//Signatures

sig User{
	reservation: set Reservation
}

sig Reservation{
	car: one Car,
	user: one User,
	time: one Time,
	date: one Date
}

sig Position{
}

sig Car{
	code: one Int,
	plate: String,
	position: one Position,
	available: Bool 
	battery level: Int
}

sig Ride{
	driver: one User,
	car: one Car,
	time: one Time,
	date: one Date

}

sig SafeArea{
	area: seq Position
}

sig PowerGridStation{
	position: one Position,
	availability: one Int
}{
	availability>0 or availability=0
}

sig Operator{
	operation: set Operation
}

sig Operation{}

//facts

// Cars have an unique code
fact uniqueCodes{
	all c1,c2: Car | (c1 != c2) => c1.code != c2.code
}

fact twoCarWithSamePosition{
	all c1,c2: Car | (c1!=c2) => c1.position!=c2.position
}



// un utente che effettua una ride deve aver fatto una prenotazione della stessa macchina
// ogni macchina available deve essere in una safe area

//predicates

