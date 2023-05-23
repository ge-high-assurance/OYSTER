import subprocess
import xml.etree.ElementTree as ET
import json
from sklearn.svm import SVC
import pandas as pd
import pickle
import numpy as np
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
import sys
import shutil
import random
from xml.dom import minidom
import xml
import signal
from contextlib import contextmanager

class TimeoutException(Exception): pass

@contextmanager
def time_limit(seconds):
    def signal_handler(signum, frame):
        raise TimeoutException("Timed out!")
    signal.signal(signal.SIGALRM, signal_handler)
    signal.alarm(seconds)
    try:
        yield
    finally:
        signal.alarm(0)

def register_namespace(prefix, uri):
    xml.etree.ElementTree._namespace_map[uri] = prefix
def register_all_namespaces(filename):
    namespaces = dict([node for _, node in ET.iterparse(filename, events=['start-ns'])])
    for ns in namespaces:
        register_namespace(ns, namespaces[ns])

def parse_xml(xml_file):

    tree = ET.parse(xml_file)
    #tree = ET.parse("FuelControlSystem_Behavior.xml")

    root = tree.getroot()

    lis = []
    n_app = len(root)
    n_app -= 3

    applist = []
    apps = root[-2][0]
    i = 0

    while i < n_app:
        appdic = {}
        app = apps[i]
        j = 0
        while j < len(app):
            if len(app[j]) == 0:
                j += 1
                continue
            if app[j][0].text == "name":
                appdic["name"] = app[j][2].text
            elif app[j][0].text == "priority":
                appdic["priority"] = int(app[j][2].text)
            elif app[j][0].text == "priorityGroup":
                appdic["priorityGroup"] = int(app[j][2].text)
            j += 1
        applist.append(appdic)
        i += 1

    properties = root[-3][-1]
    n_properties = len(properties)
    property_lis = []
    i = 0
    while i < n_properties:
        property_lis.append(properties[i][0].text)
        i += 1

    flow = root[-1]

    i = 0
    while i < len(flow):
        if "major_frame" in flow[i][0].text:
            major_frame = int(flow[i][2][0].text)
        elif "_start_time" in flow[i][0].text:
            text = flow[i][0].text
            text = text.split("_start_time")
            j = 0
            while j < len(applist):
                if applist[j]["name"] == text[0]:
                    applist[j]["start_time"] = int(flow[i][2][0].text)
                j += 1
        elif "_repeat_period" in flow[i][0].text:
            text = flow[i][0].text
            text = text.split("_repeat_period")
            j = 0
            while j < len(applist):
                if applist[j]["name"] == text[0]:
                    applist[j]["repeat_period"] = int(flow[i][2][0].text)
                j += 1
        elif "_computetime" in flow[i][0].text:
            text = flow[i][0].text
            text = text.split("_computetime")
            j = 0
            while j < len(applist):
                if applist[j]["name"] == text[0]:
                    applist[j]["computetime"] = int(flow[i][2][0].text)
                j += 1
        i += 1
    return (applist, property_lis, major_frame)


def get_graph2vec_feature(n_files, xml_prefix, graph2vec_input):

    print("Parsing xml")
    number_of_files = n_files
    counter = 0
    max_start_time = 101
    revdic = {}

    dictionary = []
    i = 0
    while i < 1000:
        dictionary.append(str(i))
        i += 1
    while counter < number_of_files:
        tree = ET.parse( xml_prefix + str(counter) + ".xml")
        root = tree.getroot()
        queue = []
        queue.append(root)
        while queue:
            node = queue[0]
            queue = queue[1:]
            if node.text not in dictionary:
                dictionary.append(node.text)
            for child in node:
                queue.append(child)
        i = 0
        while i < len(dictionary):
            revdic[dictionary[i]] = i
            i += 1

        queue.append(root)
        ind_queue = [0]
        i = 0
        features_dic = {}
        edgelis = []
        while queue:
            node = queue[0]
            ind = ind_queue[0]
            queue = queue[1:]
            ind_queue = ind_queue[1:]
            features_dic[ind] = revdic[node.text]
            for child in node:
                i += 1
                edgelis.append([ind, i])
                queue.append(child)
                ind_queue.append(i)
        res = {}
        res["edges"] = edgelis
        res["features"] = features_dic

        json_string = json.dumps(res)
        oup = open(graph2vec_input + str(counter) + ".json", "w")
        oup.write(json_string)
        oup.close()


        #print(json_string)
        counter += 1
    print("Done")

def find_start_time(stimelis, x, y):
    starttime = random.randint(x, y)
    while starttime in stimelis:
        starttime = random.randint(x, y)
    return starttime

def generating(inpxml, train_prefix , start_count, apps, major_frame, applis):
    register_all_namespaces(inpxml)
    tree = ET.parse(inpxml)

    root = tree.getroot()
    #lines = [5000, 5027, 5054, 5081, 5108, 5135]
    generate_total = 100

    priority_groups = []
    for app in applis:
        priority_groups.append(app["priorityGroup"])
    priority_groups = sorted(list(set(priority_groups)))

    i = 0
    while i < generate_total:
        res = []
        stimelis = []
        reset = 0

        for group in priority_groups:
            app_in_group = []
            for app in applis:
                if app["priorityGroup"] == group:
                    app_in_group.append(app)
            afloatapp = []
            for app in app_in_group:
                if app["priority"] == 0:
                    afloatapp.append(app)

            fixapp = []
            for app in app_in_group:
                if app["name"][4:] not in apps:
                    fixapp.append(app)
            ignored = []
            for app in fixapp:
                if app in afloatapp:
                    fixapp.remove(app)
                    ignored.append(app)
                    stimelis.append(app["start_time"])
                    res.append(app)
            if len(fixapp) > 0:
                prilis = []
                start_lis = []
                for app in fixapp:
                    prilis.append(app["priority"])
                    start_lis.append(app["start_time"])
                    stimelis.append(app["start_time"])
                prilis = sorted(prilis)
                start_lis = sorted(start_lis)
                for app in fixapp:
                    j = 0
                    while j < len(prilis):
                        if app["priority"] == prilis[j]:
                            app["start_time"] = start_lis[j]
                        j += 1
                    res.append(app)

                for app in app_in_group:
                    if (app not in fixapp) and (app not in ignored):
                        priority = app["priority"]
                        if priority <= prilis[0]:
                            try:
                                with time_limit(1):
                                    starttime = find_start_time(stimelis, 0, start_lis[0])
                            except TimeoutException as e:
                                reset = 1
                                break


                            stimelis.append(starttime)
                            prilis.append(priority)
                            prilis = sorted(prilis)
                            start_lis.append(starttime)
                            start_lis = sorted(start_lis)
                            app["start_time"] = starttime
                            res.append(app)
                        elif priority >= prilis[-1]:
                            try:
                                with time_limit(1):
                                    starttime = find_start_time(stimelis, start_lis[-1], major_frame)
                            except TimeoutException as e:
                                reset = 1
                                break



                            stimelis.append(starttime)
                            prilis.append(priority)
                            prilis = sorted(prilis)
                            start_lis.append(starttime)
                            start_lis = sorted(start_lis)
                            app["start_time"] = starttime
                            res.append(app)
                        else:
                            j = 0

                            while priority > prilis[j]:
                                j += 1

                            if start_lis[j] - start_lis[j - 1] <= 1:
                                reset = 1
                                break
                            starttime = find_start_time(stimelis, start_lis[j - 1], start_lis[j])

                            stimelis.append(starttime)
                            prilis.append(priority)
                            prilis = sorted(prilis)
                            start_lis.append(starttime)
                            start_lis = sorted(start_lis)
                            app["start_time"] = starttime
                            res.append(app)
                if reset == 1:
                    break

            elif fixapp == []:
                prilis = []
                start_lis = []
                for app in ignored:
                    app_in_group.remove(app)
                for app in app_in_group:
                    prilis.append(app["priority"])
                while len(start_lis) < len(prilis):
                    ran = random.randint(0, major_frame)
                    if ran not in stimelis:
                        start_lis.append(ran)
                        stimelis.append(ran)
                prilis = sorted(prilis)
                start_lis = sorted(start_lis)
                for app in app_in_group:
                    j = 0
                    while j < len(prilis):
                        if app["priority"] == prilis[j]:
                            app["start_time"] = start_lis[j]
                        j += 1
                    res.append(app)
        if reset == 1:
            continue
        j = 0
        while j < len(root[-1]):
            if "_start_time" in root[-1][j][0].text:
                text = root[-1][j][0].text
                text = text.split("_start_time")
                text = text[0]
                for app in res:
                    if app["name"] == text:
                        starttime = str(app["start_time"])
                    root[-1][j][2][0].text = starttime

            j += 1


        oup = open(train_prefix + str(start_count + i) + ".xml", "wb")
        
        tree.write(oup, encoding="utf-8")
        oup.close()
        i += 1



def get_falsifiable_index(propertylis, crv_output):

    falsifiable_property = []
    tree = ET.parse(crv_output)
    root = tree.getroot()
    for child in root:
        if child.tag == "Property":
            flag = 0
            for grand_child in child:
                if grand_child.text == "falsifiable":
                    flag = 1
            if flag == 1:
                property_name = child.attrib["name"]
                property_name = property_name.split(":")
                property_name = property_name[0]
                property_name = property_name[1:]
                falsifiable_property.append(int(property_name))
    falsifiable_app = []
    for propertyind in falsifiable_property:
        for prop in propertylis:
            if "P" + str(propertyind) + ":" in prop:
                prop = prop.split(" ")
                app1 = prop[2]
                app2 = prop[4]
                if app1 not in falsifiable_app:
                    falsifiable_app.append(app1)
                if app2 not in falsifiable_app:
                    falsifiable_app.append(app2)

    return falsifiable_app


mode = 1 
if mode== 1:
    input_behavior_xml = sys.argv[1]
    n_files = int(sys.argv[2]) # Number of xml files in the training and validation dataset. 500
    train_prefix = sys.argv[3] #Location and name of the xml files. if the input is "xml_data/New_schedule" and n_files=500 the expected xml file name is from xml_data/New_schedule0.xml to xml_data/New_schedule499.xml
    graph2vec_input = sys.argv[4] #Where to store the input for the graph2vec algorithm. "dataset/"
    graph2vec_output = sys.argv[5] #Where to store the output for the graph2vec algorithm. "features/nci1.csv"
    graph2vec_loc = sys.argv[6] # location of the praph2vec library. "graph2vec1/src/graph2vec.py"
    suggestion_path = sys.argv[7]# where to save the suggestion xml. "suggestion.xml"
    label_loc = sys.argv[8]# Where to find the training labels. "labels"
    crv_output = sys.argv[9]# Where to find the crv_output file. "crv_output144.xml"
elif mode == 0:
    crv_output = "crv_output.xml"
    input_behavior_xml = "behavior.xml"
    n_files = 500
    train_prefix = "xml_data/New_schedule"
    graph2vec_input = "dataset/"
    graph2vec_output = "features/nci1.csv"
    graph2vec_loc = "graph2vec1/src/graph2vec.py"
    suggestion_path = "suggestion.xml"
    label_loc = "labels"

np.random.seed(0)
random.seed(0)

applis, propertylis, major_frame = parse_xml(input_behavior_xml)

false_system = get_falsifiable_index(propertylis, crv_output)
if false_system == []:
    root = minidom.Document()
    xml = root.createElement('root')
    root.appendChild(xml)
    productChild = root.createElement('prediction')
    productChild.setAttribute("Result", "All property already hold.")
    xml.appendChild(productChild)
else:
    """lines_all = [1554, 1581, 1608, 1635, 1662, 1689]
    lines = []
    for ind in false_system:
        lines.append(lines_all[ind])
    #labels = get_label(n_files, verdict_loc, kind2_loc, xml_prefix, crv_prefix)"""
    try:
        with time_limit(600):
            generating(input_behavior_xml, train_prefix, 400, false_system, major_frame, applis)
    except TimeoutException as e:
        print("Cannot find appropriate suggestion")



    #labels = pickle.load(open("labels", "rb"))
    labels = pickle.load(open(label_loc, "rb"))

    get_graph2vec_feature(n_files, train_prefix, graph2vec_input)


    command = "python " + graph2vec_loc + " --input-path " + graph2vec_input + " --output-path " + graph2vec_output
    ret = subprocess.run(command, capture_output=True, shell=True)
    #print(ret)

    df = pd.read_csv(graph2vec_output)

    X = df.to_numpy()
    X = X[:, 1:]
    y = labels
    y = np.array(y)
    y = y[:, 0]
    X_train = X[ : 400]
    y_train = y[: 400]
    X_test = X[ 400:]




    clf = make_pipeline(StandardScaler(), SVC(gamma='auto', probability=True))
    clf.fit(X_train, y_train)
    #print("Training Accuracy")
    #print(clf.score(X_train, y_train))
    #print("Test Accuracy")
    #print(clf.score(X_test, y_test))
    y_hat = clf.predict_proba(X_test)
    y_hat = y_hat[:, 1].tolist()
    n = y_hat.index(max(y_hat))
    #y_hat1 = clf.predict(X_train)
    #CM = confusion_matrix(y_test, y_hat)
    #CM1 = confusion_matrix(y_train, y_hat1)
    #print("Training confusion Matrix")
    #print(CM1)
    #print("Test confusion Matrix")
    #print(CM)
    #suggestion = get_suggestion(train_prefix + str(400 + n) + ".xml", false_system)
    applis, propertylis, major_frame = parse_xml(train_prefix + str(400 + n) + ".xml")
    """
    for app in applis:
        while app["start_time"] >= app["repeat_period"]:
            app["start_time"] -= app["repeat_period"]

    """

    root = minidom.Document()

    xml = root.createElement('root')
    root.appendChild(xml)

    i = 1
    #while i <= 6:


    for name in false_system:
        for app in applis:
            if name in app["name"]:
                productChild = root.createElement('prediction')
                productChild.setAttribute("id", str(i));
                productChild.setAttribute("agree-constant", app["name"] + "_start_time")
                productChild.setAttribute("suggested-value", str(app["start_time"]))
                #productChild.setAttribute(suggestion[i - 1][0], suggestion[i - 1][1])
                xml.appendChild(productChild)

                i += 1


xml_str = root.toprettyxml(indent="\t")
with open(suggestion_path, "w") as f:
    f.write(xml_str)




