import React, { useState } from 'react';
import modalConfig from './modalConfig.js'


function Modal() {

  //const configParsed = JSON.parse(modalConfig);
  const [state, setState] = useState("problem-type");
  const [modelTitle, setModelTitle] = useState(modalConfig['problem-type'].title);
  const [problemsName, setFirstNameError] = useState("");
  const [buttonsName, setButtonsName] = useState(modalConfig['problem-type'].buttonsName);

  function goToNextState(id) {
    const nextState = modalConfig[state]['next:']
    setState(nextState)

  }

  return (
    <div className="modal fade" id="exampleModal" tabIndex="-1" aria-labelledby="exampleModalLabel" aria-hidden="true">
      <div className="modal-dialog">
        <div className="modal-content">
          <div className="modal-header text-center">
            <h5 className="modal-title text-center" id="exampleModalLabel">{modelTitle}</h5>
            <button type="button" className="btn-close" data-bs-dismiss="modal" aria-label="Close"></button>
          </div>
          <div className="modal-body">
            <div className="container">
              <div className="row justify-content-center">
                <div className="btn-group" role="group" aria-label="Basic outlined example">
                  {buttonsName.map((buttonName) => {
                    return (
                      <button type="button" id={buttonName} className="btn btn-outline-primary btn-lg btn-block" onClick={event => goToNextState(event.target.id)}>{buttonName}</button>
                    )
                  })}
                </div>
              </div>
            </div>
          </div>
          <div className="modal-footer">
            <button type="button" className="btn btn-secondary" data-bs-dismiss="modal">View Rule</button>
            <button type="button" className="btn btn-outline-primary">Next</button>
          </div>
        </div>
      </div>
    </div>
  )
}


export default Modal;

//react cycle: choose problem -> choose variable -> choose operator -> choose state -> continue? -> choose variable -> ... 