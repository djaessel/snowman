#include "classreader.h"
#include "classstorer.h"
#include <QDir>

void ClassReader::readClasses()
{
  this->classes.clear();

  for (const auto & entry : fs::directory_iterator(ClassStorer::ExportDir.toStdString().c_str()))
  {
    QString fileP = QString(entry.path().generic_string().c_str());
    if (fileP.endsWith(".cpp"))
    {
        QString className = fileP.split('.')[0].split(QDir::separator()).back(); // remove file extension to get class name for now
        this->classes.insert_or_assign(className, FixedClass(className));

        QFile file(fileP);
        if(!file.open(QIODevice::ReadOnly)) {
            cout << "CLASSREADER ERROR: File could not be opened - " << fileP.toStdString().c_str() << endl;
        }

        bool funcBody = false;
        QString curFuncName = nullptr;
        FixedFunction curFunc(nullptr);
        QTextStream in(&file);
        while(!in.atEnd()) {
            QString line = in.readLine().remove(QRegExp("([\n]{1})$"));
            if (line.contains(className + "::")) {
                curFuncName = line.split("::")[1].split("(")[0];
                curFunc = FixedFunction(curFuncName);
                funcBody = true;
            } else if (funcBody) {
                curFunc.addCodeLine(line);
                if (line.remove(QRegExp("([\n]+)$")) == QString("}")) {
                    this->classes[className].addFunction(curFunc);
                    curFuncName = nullptr;
                    funcBody = false;
                }
            }
        }
        file.close();
    }
  }
}
