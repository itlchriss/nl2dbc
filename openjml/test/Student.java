/**
 * Represents a student enrolled in the school.
 * A student can be enrolled in many courses.
 */
public class Student {

	/**
	* The name of this student.
	* \var String name
	* The length should be always less than 10 and contain alphabets only.
	*/
	private String name;	//name should contain alphabets only.

	public static int studentNumber;
	
	/**
	* @requires name != null
	* Sets the name of this Student.
	* \param name the value should not be null. The length of the value should be less than 50.
	*/
	public void setName(String name) {
		this.name = name;
	}

	/**
	* @ensures \result.length<50
	* @ensures \result != null
	* Gets the name of this Student.
	* \return the value should not be null. The length of the value should be less than 50.
	*/
	public String getName() {
		return name;
	}

	/**
	* @requires number>0 && number<100
	* Sets the studentNumber of this Student.
	*  \param number the value should be greater than zero and less than 100.
	*/
	public static int setStudentNumber(int number) {
        studentNumber = number;
        return studentNumber;
	}


    //@ ensures studentNumber == 1;
    public static void main(String[] args) {
    setStudentNumber(1);
    return;
    }

}
