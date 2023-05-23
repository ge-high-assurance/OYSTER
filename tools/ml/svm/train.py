import subprocess
import xml.etree.ElementTree as ET
import json
from sklearn.svm import SVC
import pandas as pd
import pickle
import numpy as np
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import confusion_matrix
import sys


def get_label(n_files, verdict_loc, kind2_loc, xml_prefix, crv_output):
    i = 0
    run_total = n_files
    labels = []
    while i < run_total:

        command = "java --add-opens java.management/com.sun.jmx.mbeanserver=ALL-UNNAMED --add-opens java.base/java.lang=ALL-UNNAMED -jar " + verdict_loc +" --vdm " + xml_prefix + str(i) + ".xml --crv " + crv_output + str(i) +  ".xml " + kind2_loc

        print(command)
        ret = subprocess.run(command, capture_output=True, shell=True)
        print(ret.stdout.decode())

        with open(crv_output + str(i) +  ".xml") as inp:
            if "falsifiable" in inp.read():
                labels.append(0)
            else:
                labels.append(1)
        i += 1
    pickle.dump(labels, open("system_labels", "wb"))
    return labels


def get_graph2vec_feature(n_files, xml_prefix, graph2vec_input):

    print("Parsing xml")
    number_of_files = n_files
    counter = 0
    max_start_time = 101
    while counter < number_of_files:
        tree = ET.parse( xml_prefix + str(counter) + ".xml")

        root = tree.getroot()


        queue = []
        revdic = {}



        dictionary = []

        i = 0

        while i < max_start_time:
            dictionary.append(str(i))
            i += 1
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

mode = 0
if mode == 1:
    n_files = int(sys.argv[1]) # Number of xml files in the training and validation dataset. 500
    verdict_loc = sys.argv[2] #Location of the verdict jar. "/home/chi/Programs/VERDICT/extern/verdict-bundle-app-1.0.0-SNAPSHOT-capsule.jar"
    kind2_loc = sys.argv[3] #Location of the kind2 binary. "/home/chi/Programs/VERDICT/extern/nix/kind2"
    xml_prefix = sys.argv[4] #Location and name of the xml files. if the input is "xml_data/New_schedule" and n_files=500 the expected xml file name is from xml_data/New_schedule0.xml to xml_data/New_schedule499.xml
    crv_prefix = sys.argv[5] #Location and name of the output crv files. for example if the input is "tmp/crv_output", the output would be like tmp/crv_output0.xml and so on.
    graph2vec_input = sys.argv[6] #Where to store the input for the graph2vec algorithm. "dataset/"
    graph2vec_output = sys.argv[7] #Where to store the output for the graph2vec algorithm. "features/nci1.csv"
    svm_model_loc = sys.argv[8] #Where to save the SVM model. "SVM.model"
    graph2vec_loc = sys.argv[9] # location of the praph2vec library. "graph2vec1/src/graph2vec.py"
    test_split = float(sys.argv[10]) # The ratio between training and validation data. 0.9
elif mode == 0:
    n_files = 500
    verdict_loc = "/home/chi/Programs/VERDICT/extern/verdict-bundle-app-1.0.0-SNAPSHOT-capsule.jar"
    kind2_loc =  "/home/chi/Programs/VERDICT/extern/nix/kind2"
    xml_prefix = "xml_data/New_schedule"
    crv_prefix = "tmp/crv_output"
    graph2vec_input =  "dataset/"
    graph2vec_output = "features/nci1.csv"
    svm_model_loc = "SVM.model"
    graph2vec_loc = "graph2vec1/src/graph2vec.py"
    test_split = 0.9

labels = get_label(n_files, verdict_loc, kind2_loc, xml_prefix, crv_prefix)
#labels = pickle.load(open("labels", "rb"))
"""
get_graph2vec_feature(n_files, xml_prefix, graph2vec_input)

command = "python " + graph2vec_loc + " --input-path " + graph2vec_input + " --output-path " + graph2vec_output + " --train True"
ret = subprocess.run(command, capture_output=True, shell=True)
print(ret)

df = pd.read_csv(graph2vec_output)

X = df.to_numpy()
X = X[:, 1:]
y = labels
y = np.array(y)
X_train = X[ : int(n_files * test_split)]
X_test = X[ int(n_files * test_split):]

i = 0
while i < y.shape[1]:

    
    y_train = y[: int(n_files * test_split), i]
    y_test = y[ int(n_files * test_split):, i]



    clf = make_pipeline(StandardScaler(), SVC(gamma='auto'))
    clf.fit(X_train, y_train)
    print("Training Accuracy")
    print(clf.score(X_train, y_train))
    print("Test Accuracy")
    print(clf.score(X_test, y_test))
    y_hat = clf.predict(X_test)
    y_hat1 = clf.predict(X_train)
    CM = confusion_matrix(y_test, y_hat)
    CM1 = confusion_matrix(y_train, y_hat1)
    print("Training confusion Matrix")
    print(CM1)
    print("Test confusion Matrix")
    print(CM)
    pickle.dump(clf, open(svm_model_loc + str(i), "wb"))

    i += 1
"""