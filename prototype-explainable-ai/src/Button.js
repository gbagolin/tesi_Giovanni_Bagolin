import React, { useState } from 'react';

function Button() {
    return (
        <div className="row justify-content-center margin-top">
            <button type="button" className="btn button" data-bs-toggle="modal" data-bs-target="#exampleModal">Write a rule</button>
        </div>
    )
}


export default Button;