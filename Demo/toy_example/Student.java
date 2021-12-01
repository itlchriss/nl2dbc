public class Student {
/**
* \var String name
* The length of the value should always be less than 50.
*/
public String name;
/**
* \var String studentNumber
* The value should always be greater than 0 and less than 100.
*/
public int studentNumber;

public Student() {
this.name = "a";
this.studentNumber = 1;
}
/**
* Sets the name of this Student.
* \param name the value should not be null. The length of the value should be less than 100.
*/
public void setName(String name) {
name = name;
}
/**
* Gets the name of this Student.
* \return the value should not be null. The length of the value should be less than 50.
*/
public String getName() {
return this.name;
}
/**
* Sets the studentNumber of this Student.
* \param number the value should be greater than zero and less than 100.
*/
public void setStudentNumber(int number) {
studentNumber = number;
}

public static void main(String[] args) {
Student s = new Student();
s.setName("Mary");
s.setStudentNumber(200);
return;
}
}

