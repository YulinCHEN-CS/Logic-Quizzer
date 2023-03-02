# Written by Stephen Chen at 2023.02.25
import random
import sys
import tkinter as tk
from time import sleep
from tkinter.messagebox import *
import re as regular  # no idea there seems to have another re.py
from sympy.parsing.sympy_parser import parse_expr
import sympy.abc
import sympy
from sympy.logic.boolalg import to_dnf, is_dnf
from sympy.logic.inference import satisfiable, valid

window_size = "800x600"
window_width = 800
window_height = 600
teacher = "Teacher"
student = "Student"
append = "APPEND"
test = "TEST"
practice = "PRACTICE"
question_file_name = "questions.txt"
TIME_EXPECTED_FOR_A_QUESTION = 60


# put the window to the center of screen
def center_window(window, w, h):
    ws = root.winfo_screenwidth()
    hs = root.winfo_screenheight()
    # calculate x, y positions
    x = (ws / 2) - (w / 2)
    y = (hs / 2) - (h / 2)
    window.geometry('%dx%d+%d+%d' % (w, h, x, y))


class LogicQuizzer:
    def __init__(self, root):
        # Global
        self.start_window = root  # window for start window
        self.question_ui = None  # window for question and answer also for appending question
        self.question_type_var = None  # question type been selected
        self.current_user_type = None  # String; store current user type
        self.user_type_var = None  # tk.StringVar(); used to store usr typing for their type
        self.user_types = [teacher, student]

        self.question_mode_var = None  # tk.StringVar(), used to store "TEST" or "PRACTICE"
        self.question_modes = [append, test, practice]
        self.mode = None

        self.num_question_var = None
        self.num_can_be_chosen = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        self.num_of_question = 0

        self.required_type = None  # question type required by user
        # define question type and corresponding solution
        self.question_types = {
            "Truth Table": self.show_truth_table,
            "DNF Form": self.convert_to_dnf,
            "Satisfiability": self.check_satisfiability,
            "Validity": self.check_validity,
        }

        # Student window
        self.question_content_label = None  # question content
        self.status_label = None  # question "Correct" or not
        self.answer_entry = None  # tk.text to enable multiple lines entry
        self.correct_answer = None  # correct answer
        self.questions = {}  # all the question
        self.current_question = None  # current question tuple([0]: type, [1]: content, [2]: formula)
        self.current_question_index = 0  # current question index
        self.remaining_time_var = None
        self.timer = None

        self.test_result = []
        # Teacher window
        self.submit_label = None  # Question written into file successfully or not
        # self.formula_var = None  # Store formula user typed in
        # self.question_var = None  # Store question content user typed in
        self.formula_entry = None  # Store formula user typed in
        self.content_entry = None  # Store question content user typed in

    # Create start window
    def start(self):
        self.start_window.title("Propositional Logic Quizzer")
        center_window(self.start_window, window_width, window_height)

        select_type_label = tk.Label(self.start_window, text="Who are you:")
        select_type_label.pack()

        self.user_type_var = tk.StringVar()
        self.user_type_var.set(self.user_types[0])

        user_type_manu = tk.OptionMenu(self.start_window, self.user_type_var, *self.user_types)
        user_type_manu.pack()

        select_type_label = tk.Label(self.start_window, text="Select question type:")
        select_type_label.pack()

        self.question_type_var = tk.StringVar()
        self.question_type_var.set(list(self.question_types.keys())[0])
        question_type_menu = tk.OptionMenu(self.start_window, self.question_type_var, *self.question_types.keys())
        question_type_menu.pack()

        select_num_label = tk.Label(self.start_window, text="Select number of question:")
        select_num_label.pack()

        self.num_question_var = tk.StringVar()
        self.num_question_var.set(self.num_can_be_chosen[0].__str__())
        question_num_manu = tk.OptionMenu(self.start_window, self.num_question_var, *self.num_can_be_chosen)
        question_num_manu.pack()

        select_mode_label = tk.Label(self.start_window, text="Select mode:")
        select_mode_label.pack()

        self.question_mode_var = tk.StringVar()
        self.question_mode_var.set(self.question_modes[0])
        question_mode_menu = tk.OptionMenu(self.start_window, self.question_mode_var, *self.question_modes)
        question_mode_menu.pack()

        # create start button
        start_button = tk.Button(self.start_window, text="Start", command=self.start_quiz)
        start_button.pack()

        quit_button = tk.Button(self.start_window, text="Quit", command=sys.exit)
        quit_button.pack()

    # Create the question answer window for students
    def question_practice(self):
        self.question_ui.deiconify()  # show the hidden window
        self.question_ui.title("Propositional Logic Quizzer Practice")
        center_window(self.question_ui, window_width, window_height)
        # self.answer_var = tk.StringVar()

        self.question_content_label = tk.Label(self.question_ui, text="")
        self.question_content_label.pack()

        # answer_entry = tk.Entry(self.question_ui, textvariable=self.answer_var)
        # answer_entry.pack()

        self.answer_entry = tk.Text(self.question_ui, width=30, height=12, font=("Helvetica", 16))
        self.answer_entry.pack()

        submit_button = tk.Button(self.question_ui, text="Submit", command=self.check_answer)
        submit_button.pack()

        self.status_label = tk.Label(self.question_ui, text="")
        self.status_label.pack()

        next_button = tk.Button(self.question_ui, text="Next", command=self.answer_next_question)
        next_button.pack()

    def question_test(self):
        self.question_ui.deiconify()  # show the hidden window
        self.question_ui.title("Propositional Logic Quizzer Test")
        center_window(self.question_ui, window_width, window_height)

        self.question_content_label = tk.Label(self.question_ui, text="")
        self.question_content_label.pack()

        self.answer_entry = tk.Text(self.question_ui, width=30, height=12, font=("Helvetica", 16))
        self.answer_entry.pack()

        select_time_label = tk.Label(self.question_ui, text="Remaining time:")
        select_time_label.pack()

        self.remaining_time_var = tk.StringVar()
        self.timer = tk.Label(self.question_ui, textvariable=self.remaining_time_var)
        self.timer.pack()

        self.status_label = tk.Label(self.question_ui, text="")
        self.status_label.pack()

        test_next_button = tk.Button(self.question_ui, text="Next",
                                     command=lambda: [self.check_answer(), self.answer_next_question()])
        test_next_button.pack()

    def test_result_window(self):
        self.question_ui.title("Propositional Logic Quizzer Test Result")
        center_window(self.question_ui, window_width, window_height)

        result = ""
        if len(self.test_result) == 0:
            question_mark_label = tk.Label(self.question_ui, text="all is right")
            question_mark_label.pack()
        else:
            print(len(self.test_result))
            print(len(self.questions.keys()))
            rate = (1 - len(self.test_result) / len(self.questions.keys())) * 100
            question_mark_label = tk.Label(self.question_ui, text="Mark: %.2f\n" % rate)
            question_mark_label.pack()

            for record in self.test_result:
                result += "Question No.: {}, Question type: {}\nQuestion content: {}\nYour answer: {}\nCorrect answer: {}\n".format(
                    record[0], record[1][0], record[1][1] + record[1][2], record[2], record[3])
            result_label = tk.Label(self.question_ui, text=result)
            result_label.pack()
        back_home_button = tk.Button(self.question_ui, text="Back to Home page", command=self.back_home)
        back_home_button.pack()

    # Create the question append window for teachers
    def question_appender(self):
        self.question_ui.deiconify()
        self.question_ui.title("Propositional Logic Quizzer")
        center_window(self.question_ui, window_width, window_height)
        # self.question_var = tk.StringVar()
        # self.formula_var = tk.StringVar()

        question_content_prompt = tk.Label(self.question_ui, text="Enter question content: ")
        question_content_prompt.pack()

        self.content_entry = tk.Text(self.question_ui, width=30, height=10, font=("Helvetica", 16))
        self.content_entry.pack()

        question_formula_prompt = tk.Label(self.question_ui, text="Enter question formula: ")
        question_formula_prompt.pack()

        # formula_entry = tk.Entry(self.question_ui, textvariable=self.formula_var)
        # formula_entry.pack()

        self.formula_entry = tk.Text(self.question_ui, width=30, height=5, font=("Helvetica", 16))
        self.formula_entry.pack()

        submit_button = tk.Button(self.question_ui, text="Submit",
                                  command=lambda: self.write_question(question_file_name))
        submit_button.pack()

        self.submit_label = tk.Label(self.question_ui, text="")
        self.submit_label.pack()

        next_button = tk.Button(self.question_ui, text="Next", command=self.append_next_question)
        next_button.pack()

        back_home_button = tk.Button(self.question_ui, text="Back to Home page", command=self.back_home)
        back_home_button.pack()

    # Append question into file
    def write_question(self, filename):
        question_tuple = [self.required_type, self.content_entry.get("1.0", "end - 1 chars"),
                          self.formula_entry.get("1.0", "end - 1 chars")]
        contain_empty = False
        for item in question_tuple:
            if item == "":
                contain_empty = True
        print(question_tuple)
        if not contain_empty:
            with open(filename, "a") as f:
                for items in question_tuple:
                    f.write(items + '\n')
            self.submit_label.config(text="Success")
        else:
            self.submit_label.config(text="Wops! Something went wrong")

    # Renew question append window
    def append_next_question(self):
        # self.question_var = ""
        # self.formula_var = ""
        self.content_entry.delete("1.0", "end - 1 chars")
        self.formula_entry.delete("1.0", "end - 1 chars")

    # Back to the start page
    def back_home(self):
        self.current_question_index = 0
        self.test_result = []
        self.question_ui.destroy()
        self.start_window.deiconify()

    def show_test_result(self):
        self.question_ui.destroy()
        self.question_ui = tk.Tk()
        self.test_result_window()

    # read question from the file
    def load_questions(self, filename):
        self.questions = {}
        with open(filename, "r") as f:
            index = 0
            question_tuple = []
            for line in f:
                line = line.strip()
                if not line:
                    continue
                question_tuple.append(line)
                if index % 3 == 2:
                    if question_tuple[0] == self.required_type:  # ensure the type is correct
                        self.questions[index // 3] = question_tuple  # [0] : type, [1]: question, [2]: formula
                    else:
                        index -= 3
                    question_tuple = []
                index += 1
        print(self.question_type_var.get())
        print(self.required_type)
        print(self.questions)

    # Renew question answer window
    def answer_next_question(self):
        self.answer_entry.delete("1.0", "end")
        self.status_label.config(text="")
        if self.current_question_index < self.num_of_question:
            self.current_question = self.questions.get(list(self.questions.keys())[self.current_question_index])
            self.current_question_index += 1
            print(len(self.questions))
            print("index: ", self.current_question_index)
            print("current Q: ", self.current_question)
            self.question_content_label.config(text="Q{}/{}: {}".format(self.current_question_index,
                                                                        len(self.questions),
                                                                        self.current_question[1] + "\n" +
                                                                        self.current_question[2]))
            self.question_ui.update()
            print(self.current_question)
        else:
            if self.mode == practice:
                self.back_home()
                result = showwarning('Prompt', 'You have completed all the questions, please try other fields.')
                print(f'prompt: {result}')
            else:
                self.show_test_result()

    def start_timer(self, time):
        for i in range(time, 0, -1):
            if self.current_question_index <= len(self.questions):
                self.remaining_time_var.set(i.__str__() + " s")
                self.question_ui.update()
                sleep(1)
        while self.current_question_index < len(self.questions):
            self.answer_next_question()
        self.show_test_result()

    def prompt_invalid(self, message):
        self.back_home()
        invalid = showwarning('Prompt', message)
        print(f'prompt: {invalid}')

    def shuffle_question(self):
        shuffled_dict = {}
        keys = list(self.questions.keys())
        random.shuffle(keys)
        for i in range(self.num_of_question):
            shuffled_dict[keys[i]] = self.questions.get(keys[i])
        self.questions = shuffled_dict
        print(self.questions)

    def switch_mode(self):
        if self.mode == append:
            if self.current_user_type == student:
                self.prompt_invalid("Student has no access to append question")
            else:
                self.question_appender()
        else:
            self.load_questions(question_file_name)
            if self.num_of_question > len(self.questions):
                self.prompt_invalid("No enough question")
            else:
                self.shuffle_question()
                if self.mode == practice:
                    self.question_practice()
                    self.answer_next_question()
                else:
                    remaining_time = self.num_of_question * TIME_EXPECTED_FOR_A_QUESTION
                    self.question_test()
                    self.answer_next_question()
                    self.start_timer(remaining_time)

    # Start our app
    def start_quiz(self):
        self.start_window.withdraw()
        self.question_ui = tk.Toplevel()
        self.current_user_type = self.user_type_var.get()
        self.required_type = self.question_type_var.get()
        self.mode = self.question_mode_var.get()
        self.num_of_question = int(self.num_question_var.get())
        self.switch_mode()
        print(self.current_question_index)
        print(self.current_user_type)

    # Check answer automatically
    def check_answer(self):
        # answer = self.answer_var.get()
        answer = self.answer_entry.get("1.0", "end - 1 chars")
        answer_copy = answer
        is_dnf_form = True
        current_type = self.current_question[0]
        current_formula = self.current_question[2]
        solution = self.question_types[current_type]

        if current_type == "DNF Form" and answer != "":  # Special case if user did not enter simplest dnf
            is_dnf_form = is_dnf(answer)
            answer = to_dnf(answer, True).__str__()
        answer = ''.join(answer.split())

        solution(current_formula)
        correct_copy = ''.join(self.correct_answer.split())
        print(answer.lower())
        print(correct_copy.lower())
        if answer.lower().lower() == correct_copy.lower() and is_dnf_form:
            if self.mode == practice:
                self.status_label.config(text="Correct")
        else:
            if self.mode == practice:
                self.status_label.config(text="Incorrect\n" + "Suggested answer: \n" + self.correct_answer)
            else:
                self.test_result.append([self.current_question_index, self.current_question, answer_copy,
                                         self.correct_answer])

    # Generate Truth table
    def show_truth_table(self, expression):
        self.correct_answer = ""
        propositions = regular.split(r'[^A-Za-z]', expression)  # remove connectives
        propositions = [item for item in propositions if item != '']  # remove empty propositions
        propositions = list(set(propositions))  # remove repeated propositions
        truth_table = sympy.logic.boolalg.truth_table(expression, propositions)
        for item in truth_table:
            self.correct_answer += "{0} -> {1}\n".format(*item)
        print(self.correct_answer)

    # Generate Dnf expression
    def convert_to_dnf(self, expression):
        dnf_expr = to_dnf(expression, True)
        self.correct_answer = dnf_expr.__str__()

    # Check the satisfiability
    def check_satisfiability(self, expression):
        sympy_expr = parse_expr(expression)
        if satisfiable(sympy_expr):
            self.correct_answer = "Satisfiable"
        else:
            self.correct_answer = "Unsatisfiable"

    # Check the validity
    def check_validity(self, expression):
        sympy_expr = parse_expr(expression)
        if valid(sympy_expr):
            self.correct_answer = "Valid"
        else:
            self.correct_answer = "Invalid"


# main
if __name__ == "__main__":
    root = tk.Tk()
    app = LogicQuizzer(root)
    app.start()
    root.mainloop()
